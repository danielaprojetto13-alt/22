import argparse
import os
import time
import re
import unicodedata
import json
import asyncio
import logging
from playwright.async_api import async_playwright

MOBILE_UA = "Mozilla/5.0 (Linux; Android 13; vivo V60) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/119.0.0.0 Mobile Safari/537.36"

MOBILE_VIEWPORT = {"width": 412, "height": 915}  # Typical Android phone size

LAUNCH_ARGS = [
    "--disable-dev-shm-usage",
    "--no-sandbox",
    "--disable-gpu",
    "--disable-extensions",
    "--disable-sync",
    "--disable-background-networking",
    "--disable-background-timer-throttling",
    "--disable-renderer-backgrounding",
    "--mute-audio",
]

def sanitize_input(raw):
    """
    Fix shell-truncated input (e.g., when '&' breaks in CMD or bot execution).
    If input comes as a list (from nargs='+'), join it back into a single string.
    """
    if isinstance(raw, list):
        raw = " ".join(raw)
    return raw

def parse_messages(names_arg):
    """
    Robust parser for messages:
    - If names_arg is a .txt file, first try JSON-lines parsing (one JSON string per line, supporting multi-line messages).
    - If that fails, read the entire file content as a single block and split only on explicit separators '&' or 'and' (preserving newlines within each message for ASCII art).
    - For direct string input, treat as single block and split only on separators.
    This ensures ASCII art (multi-line blocks without separators) is preserved as a single message.
    """
    # Handle argparse nargs possibly producing a list
    if isinstance(names_arg, list):
        names_arg = " ".join(names_arg)

    content = None  
    is_file = isinstance(names_arg, str) and names_arg.endswith('.txt') and os.path.exists(names_arg)  

    if is_file:  
        # Try JSON-lines first (each line is a JSON-encoded string, possibly with \n for multi-line)  
        try:  
            msgs = []  
            with open(names_arg, 'r', encoding='utf-8') as f:  
                lines = [ln.rstrip('\n') for ln in f if ln.strip()]  # Skip empty lines  
            for ln in lines:  
                m = json.loads(ln)  
                if isinstance(m, str):  
                    msgs.append(m)  
                else:  
                    raise ValueError("JSON line is not a string")  
            if msgs:  
                # Normalize each message (preserve \n for art)  
                out = []  
                for m in msgs:  
                    #m = unicodedata.normalize("NFKC", m)  
                    #m = re.sub(r'[\u200B-\u200F\uFEFF\u202A-\u202E\u2060-\u206F]', '', m)  
                    out.append(m)  
                return out  
        except Exception:  
            pass  # Fall through to block parsing on any error  

        # Fallback: read entire file as one block for separator-based splitting  
        try:  
            with open(names_arg, 'r', encoding='utf-8') as f:  
                content = f.read()  
        except Exception as e:  
            raise ValueError(f"Failed to read file {names_arg}: {e}")  
    else:  
        # Direct string input  
        content = str(names_arg)  

    if content is None:  
        raise ValueError("No valid content to parse")  

    # Normalize content (preserve \n for ASCII art)  
    #content = unicodedata.normalize("NFKC", content)  
    #content = content.replace("\r\n", "\n").replace("\r", "\n")  
    #content = re.sub(r'[\u200B-\u200F\uFEFF\u202A-\u202E\u2060-\u206F]', '', content)  

    # Normalize ampersand-like characters to '&' for consistent splitting  
    content = (  
        content.replace('﹠', '&')  
        .replace('＆', '&')  
        .replace('⅋', '&')  
        .replace('ꓸ', '&')  
        .replace('︔', '&')  
    )  

    # Split only on explicit separators: '&' or the word 'and' (case-insensitive, with optional whitespace)  
    # This preserves multi-line blocks like ASCII art unless explicitly separated  
    pattern = r'\s*(?:&|\band\b)\s*'  
    parts = [part.strip() for part in re.split(pattern, content, flags=re.IGNORECASE) if part.strip()]  
    return parts

async def login(args, storage_path, headless):
    """
    Async login function to handle initial Instagram login and save storage state.
    """
    try:
        async with async_playwright() as p:
            browser = await p.chromium.launch(
                headless=headless,
                args=LAUNCH_ARGS
            )
            context = await browser.new_context(
                user_agent=MOBILE_UA,
                viewport=MOBILE_VIEWPORT,
                is_mobile=True,
                has_touch=True,
                device_scale_factor=2,
                color_scheme="dark"
            )
            page = await context.new_page()
            try:
                print("Logging in to Instagram...")
                await page.goto("https://www.instagram.com/", timeout=60000)
                await page.wait_for_selector('input[name="username"]', timeout=30000)
                await page.fill('input[name="username"]', args.username)
                await page.fill('input[name="password"]', args.password)
                await page.click('button[type="submit"]')
                # Wait for successful redirect (adjust if needed for 2FA or errors)
                await page.wait_for_url("**/home**", timeout=60000)  # More specific to profile/home
                print("Login successful, saving storage state.")
                await context.storage_state(path=storage_path)
                return True
            except Exception as e:
                print(f"Login error: {e}")
                return False
            finally:
                await browser.close()
    except Exception as e:
        print(f"Unexpected login error: {e}")
        return False


async def start_swiper(session_file: str, url: str, messages: list, tabs: int = 1, delay: float = 0.02):
    """Start sending messages to the given Instagram direct URL using Playwright session_file.
    Raises Exception('Session expired') if session is invalid.
    """
    if not os.path.exists(session_file):
        raise FileNotFoundError(f"Session file not found: {session_file}")

    async with async_playwright() as p:
        browser = await p.chromium.launch(headless=True, args=LAUNCH_ARGS)
        context = await browser.new_context(storage_state=session_file, user_agent=MOBILE_UA, viewport=MOBILE_VIEWPORT, is_mobile=True, has_touch=True)

        pages = []
        for i in range(max(1, int(tabs))):
            pg = await context.new_page()
            pages.append(pg)

        async def page_worker(page):
            # Validate session on this page
            try:
                await page.goto('https://www.instagram.com/', timeout=15000)
                try:
                    await page.wait_for_selector('svg[aria-label="Home"]', timeout=5000)
                except Exception:
                    raise Exception('Session expired')

                await page.goto(url, timeout=30000)
                box = await page.wait_for_selector('[contenteditable="true"]', timeout=15000)
            except Exception as e:
                raise

            try:
                while True:
                    for msg in messages:
                        try:
                            await box.click()
                            await page.keyboard.type(msg)
                            await page.keyboard.press('Enter')
                        except Exception:
                            # if sending fails on this tab, break the inner loop and try again
                            pass
                        await asyncio.sleep(delay)
            except asyncio.CancelledError:
                return

        # Start all worker tasks
        tasks = [asyncio.create_task(page_worker(pg)) for pg in pages]

        try:
            await asyncio.gather(*tasks)
        except asyncio.CancelledError:
            for t in tasks:
                t.cancel()
            try:
                await asyncio.gather(*tasks, return_exceptions=True)
            except Exception:
                pass
        finally:
            try:
                await browser.close()
            except Exception:
                pass


async def init_page(page, url, dm_selector):
    """
    Initialize a single page by navigating to the URL with retries.
    Returns True if successful, False otherwise.
    """
    init_success = False
    for init_try in range(3):
        try:
            await page.goto("https://www.instagram.com/", timeout=60000)
            await page.goto(url, timeout=60000)
            await page.wait_for_selector(dm_selector, timeout=30000)
            init_success = True
            break
        except Exception as init_e:
            print(f"Tab for {url[:30]}... try {init_try+1}/3 failed: {init_e}")
            if init_try < 2:
                await asyncio.sleep(2)
    return init_success

async def reply_to_all_messages(page, duration=3):
    """
    SWIPE REPLY: React to incoming messages for a limited time.
    Duration: how many seconds to monitor (default 3s per message)
    """
    print(f"🔄 [REPLY_TO_ALL] Started - monitoring for {duration}s...")
    start_time = time.time()
    processed_messages = set()
    
    try:
        while time.time() - start_time < duration:
            try:
                # Find all messages in thread
                messages = await page.query_selector_all('div[role="article"]')
                if not messages:
                    messages = await page.query_selector_all('[data-testid="message-item"]')
                
                if messages:
                    # Process last 3 messages only
                    for msg in messages[-3:]:
                        msg_id = id(msg)
                        if msg_id in processed_messages:
                            continue
                        
                        try:
                            print(f"👀 [REPLY_TO_ALL] Processing message...")
                            # Hover to reveal action buttons
                            await msg.hover()
                            await asyncio.sleep(0.01)
                            
                            # Look for emoji/reaction button
                            react_btns = await msg.query_selector_all('button')
                            
                            for btn in react_btns:
                                label = await btn.get_attribute('aria-label') or ""
                                
                                # Look for reaction button
                                if any(x in label.lower() for x in ['react', 'emoji', 'like']):
                                    try:
                                        await btn.click()
                                        await asyncio.sleep(0.02)
                                        
                                        # Try to click heart emoji
                                        heart = await page.query_selector('button[aria-label*="❤"]')
                                        if heart:
                                            await heart.click()
                                            print(f"   ❤️ Heart reaction added!")
                                            processed_messages.add(msg_id)
                                            break
                                    except:
                                        continue
                        except:
                            continue
                
                await asyncio.sleep(0.1)
                
            except Exception as e:
                await asyncio.sleep(0.1)
                continue
        
        print(f"✅ [REPLY_TO_ALL] Completed after {duration}s")
        
    except Exception as e:
        print(f"❌ [REPLY_TO_ALL] Error: {e}")

async def react_message_with_hearts(page, msg_element, count=10):
    """
    React to a single message with multiple heart reactions.
    Adds up to 10 heart reactions to make it stand out.
    """
    reactions_added = 0
    try:
        for i in range(count):
            try:
                await msg_element.hover()
                await asyncio.sleep(0.03)
                
                reaction_btn = await msg_element.query_selector('button[aria-label*="react"]')
                if not reaction_btn:
                    reaction_btn = await msg_element.query_selector('div[role="button"]')
                
                if reaction_btn:
                    await reaction_btn.click()
                    await asyncio.sleep(0.03)
                    
                    # Select heart emoji
                    heart_btn = await page.query_selector('button[aria-label*="❤"]')
                    if heart_btn:
                        await heart_btn.click()
                        reactions_added += 1
                        await asyncio.sleep(0.02)
            except Exception as e:
                break
        
        return reactions_added
    except Exception as e:
        return reactions_added
async def check_and_self_react(page):
    """
    INSTANT SELF-REACT: Add 5-10 hearts to the message you just sent.
    """
    print(f"💓 [SELF_REACT] Started...")
    try:
        await asyncio.sleep(0.02)  # Brief delay for message to appear
        
        # Get last sent message
        messages = await page.query_selector_all('div[role="article"]')
        if not messages:
            messages = await page.query_selector_all('[data-testid="message-item"]')
        
        if messages:
            last_msg = messages[-1]
            print(f"💓 [SELF_REACT] Found message, adding hearts...")
            
            hearts_added = 0
            # Add 5 hearts
            for i in range(5):
                try:
                    await last_msg.hover()
                    await asyncio.sleep(0.01)
                    
                    # Find reaction button
                    react_btn = await last_msg.query_selector('button[aria-label*="Like"]')
                    if not react_btn:
                        react_btn = await last_msg.query_selector('button[aria-label*="react"]')
                    
                    if react_btn:
                        await react_btn.click()
                        await asyncio.sleep(0.02)
                        
                        # Click heart emoji
                        heart = await page.query_selector('button[aria-label*="❤"]')
                        if not heart:
                            heart = await page.query_selector('[aria-label*="❤"]')
                        
                        if heart:
                            await heart.click()
                            hearts_added += 1
                            print(f"   ❤️ +1 ({hearts_added}/5)")
                            await asyncio.sleep(0.08)
                        else:
                            break
                    else:
                        break
                except Exception as e:
                    break
            
            if hearts_added > 0:
                print(f"✅ [SELF_REACT] Done - {hearts_added} hearts added")
            return hearts_added > 0
        else:
            print(f"⚠️ [SELF_REACT] No messages found")
            return False
            
    except Exception as e:
        print(f"❌ [SELF_REACT] Error: {e}")
        return False

async def sender_instagrapi(
    cl,
    thread_id,
    messages,
    rate=8.0,
    verify_window=0.1,
    safe_rate=4.0,
    min_rate=1.0,
    failure_threshold=5,
    failure_window=30,
    cooldown=60,
):
    """
    Send messages using Instagrapi API.

    rate: desired messages per second (default 8.0)
    verify_window: seconds to wait before quick verification (default 0.1)
    safe_rate: rate to fall back to on repeated rate-limits (default 4.0)
    min_rate: minimum allowed rate (default 1.0)
    failure_threshold: number of rate errors within failure_window to trigger safe mode (default 5)
    failure_window: seconds window to count failures (default 30)
    cooldown: seconds to stay in safe mode before attempting to ramp up (default 60)
    """
    print(f"⚡ Starting Instagrapi adaptive sender for thread {thread_id} (desired_rate={rate} msg/s)")

    # Desired and current rates
    desired_rate = float(rate)
    current_rate = float(rate)
    target_interval = 1.0 / current_rate if current_rate > 0 else 1.0 / 4.0

    # Adaptive concurrency limit based on current rate, will update if rate changes
    concurrency_limit = min(256, max(8, int(current_rate * 8)))
    sem = asyncio.Semaphore(concurrency_limit)

    # Failure tracking
    from collections import deque

    failures = deque()  # stores tuples (timestamp, kind) where kind in {'rate','other'}
    safe_mode_until = 0

    async def verify_sent(msg_text):
        """Non-blocking verification: check thread contents shortly after send."""
        try:
            await asyncio.sleep(verify_window)  # quick verification window
            thread = await asyncio.to_thread(cl.direct_thread, thread_id)
            if not thread or not hasattr(thread, 'messages'):
                print("⚠️ Verify: no thread data")
                return False

            viewer_text_messages = [
                m for m in thread.messages
                if hasattr(m, 'item_type') and m.item_type == 'text'
                and hasattr(m, 'is_sent_by_viewer') and m.is_sent_by_viewer
                and hasattr(m, 'text') and m.text is not None
            ]
            if viewer_text_messages:
                last_text_msg = viewer_text_messages[0]
                if last_text_msg.text and msg_text in last_text_msg.text:
                    print(f"✅ Verified: {msg_text[:30]}...")
                    return True
            print(f"⚠️ Verify: not found for {msg_text[:30]}...")
            return False
        except Exception as e:
            print(f"⚠️ Verify error: {str(e)[:80]}")
            return False

    async def send_task(msg_text):
        """Perform send with retries inside a bounded task. Retries until success with backoff to ensure delivery."""
        nonlocal current_rate, target_interval, concurrency_limit, sem, safe_mode_until
        async with sem:
            backoff = 1.0
            attempt = 0
            while True:
                attempt += 1
                try:
                    print(f"📤 Sending message: {msg_text[:30]}... (attempt {attempt})")
                    result = await asyncio.to_thread(cl.direct_send, msg_text, thread_ids=[thread_id])
                    print(f"✅ Sent: {getattr(result, 'id', 'OK')}")

                    # Fire-and-forget verification to keep throughput
                    asyncio.create_task(verify_sent(msg_text))
                    return True

                except RateLimitError as e:
                    print(f"⚠️ Rate limit: {e}. Triggering safe mode and backing off {backoff}s.")
                    failures.append((time.time(), 'rate'))
                    # Enter safe mode
                    now = time.time()
                    safe_mode_until = max(safe_mode_until, now + cooldown)
                    # Drop current rate to safe_rate
                    current_rate = max(min(current_rate, float(safe_rate)), float(min_rate))
                    target_interval = 1.0 / current_rate if current_rate > 0 else 1.0
                    concurrency_limit = min(256, max(8, int(current_rate * 8)))
                    sem = asyncio.Semaphore(concurrency_limit)
                    await asyncio.sleep(backoff)
                    backoff = min(backoff * 2, 60)
                    continue

                except PleaseWaitFewMinutes as e:
                    print(f"⚠️ Please wait: {e}. Long backoff {backoff}s.")
                    failures.append((time.time(), 'rate'))
                    safe_mode_until = max(safe_mode_until, time.time() + cooldown)
                    current_rate = max(float(safe_rate), float(min_rate))
                    target_interval = 1.0 / current_rate if current_rate > 0 else 1.0
                    concurrency_limit = min(256, max(8, int(current_rate * 8)))
                    sem = asyncio.Semaphore(concurrency_limit)
                    await asyncio.sleep(backoff)
                    backoff = min(backoff * 2, 300)
                    continue

                except Exception as e:
                    logging.error(f"Instagrapi send error: {e}")
                    failures.append((time.time(), 'other'))
                    await asyncio.sleep(backoff)
                    backoff = min(backoff * 1.5, 30)
                    continue

    msg_index = 0

    async def monitor_and_adjust():
        """Monitor failures and adjust current_rate/target_interval over time."""
        nonlocal current_rate, target_interval, safe_mode_until, sem, concurrency_limit
        while True:
            # purge old failures
            now = time.time()
            while failures and now - failures[0][0] > failure_window:
                failures.popleft()

            # count recent 'rate' failures
            recent_rate_failures = sum(1 for t, k in failures if k == 'rate')

            # If many rate failures, ensure safe mode
            if recent_rate_failures >= int(failure_threshold) or now < safe_mode_until:
                if current_rate > float(safe_rate):
                    print(f"🔒 Entering safe mode: lowering rate to {safe_rate} msg/s due to {recent_rate_failures} recent rate failures")
                    current_rate = float(safe_rate)
                    target_interval = 1.0 / current_rate
                    concurrency_limit = min(256, max(8, int(current_rate * 8)))
                    sem = asyncio.Semaphore(concurrency_limit)
                # stay in safe mode until cooldown expires
            else:
                # If we're out of safe window and failures are low, ramp back up toward desired_rate gradually
                if current_rate < desired_rate and now >= safe_mode_until:
                    current_rate = min(desired_rate, current_rate * 1.25 + 0.5)
                    current_rate = max(current_rate, float(min_rate))
                    target_interval = 1.0 / current_rate
                    concurrency_limit = min(256, max(8, int(current_rate * 8)))
                    sem = asyncio.Semaphore(concurrency_limit)
                    print(f"⬆️ Ramping rate to {current_rate:.2f} msg/s")

            await asyncio.sleep(1)

    # start monitor
    asyncio.create_task(monitor_and_adjust())

    # Continuous scheduling loop: schedule a send task every target_interval seconds
    while True:
        msg_text = messages[msg_index]
        # Schedule send without awaiting to keep pacing
        asyncio.create_task(send_task(msg_text))

        # Advance index and sleep for the current target interval
        msg_index = (msg_index + 1) % len(messages)
        await asyncio.sleep(target_interval)

async def engage_only(storage_state, url):
    """
    ENGAGEMENT ONLY MODE: Continuously react and swipe reply to messages.
    No message sending - just pure engagement.
    Runs indefinitely until interrupted.
    """
    try:
        async with async_playwright() as p:
            browser = await p.chromium.launch(headless=True, args=LAUNCH_ARGS)
            
            # Load storage state to maintain session
            storage_json = {}
            try:
                with open(storage_state, 'r') as f:
                    storage_json = json.load(f)
            except:
                print(f"⚠️ Could not load storage state from {storage_state}")
                return
            
            context = await browser.new_context(
                storage_state=storage_json,
                user_agent=MOBILE_UA,
                viewport=MOBILE_VIEWPORT,
                is_mobile=True,
                has_touch=True
            )
            
            page = await context.new_page()
            
            print(f"🔥 ENGAGEMENT MODE - Connecting to {url}")
            try:
                await page.goto(url, timeout=30000)
                await asyncio.sleep(0.2)
            except Exception as e:
                print(f"❌ Failed to load thread: {e}")
                return
            
            print(f"✅ Connected! Monitoring for messages...")
            message_count = 0
            
            # Continuous engagement loop
            while True:
                try:
                    # Check for messages
                    messages = await page.query_selector_all('div[role="article"]')
                    if not messages:
                        messages = await page.query_selector_all('[data-testid="message-item"]')
                    
                    if messages:
                        current_count = len(messages)
                        if current_count > message_count:
                            new_messages = current_count - message_count
                            print(f"\n📨 Found {new_messages} new message(s)! Total: {current_count}")
                            message_count = current_count
                            
                            # React to new messages
                            for msg in messages[-new_messages:]:
                                try:
                                    print(f"  👀 Reacting to message...")
                                    await msg.hover()
                                    await asyncio.sleep(0.01)
                                    
                                    # Find reaction button
                                    react_btns = await msg.query_selector_all('button')
                                    for btn in react_btns:
                                        label = await btn.get_attribute('aria-label') or ""
                                        if any(x in label.lower() for x in ['react', 'emoji', 'like']):
                                            await btn.click()
                                            await asyncio.sleep(0.02)
                                            
                                            # Add hearts
                                            for heart_num in range(3):
                                                heart = await page.query_selector('button[aria-label*="❤"]')
                                                if not heart:
                                                    heart = await page.query_selector('[aria-label*="❤"]')
                                                
                                                if heart:
                                                    await heart.click()
                                                    print(f"    ❤️ Heart {heart_num + 1}/3")
                                                    await asyncio.sleep(0.02)
                                                else:
                                                    break
                                            break
                                except Exception as react_e:
                                    print(f"  ⚠️ Reaction error: {react_e}")
                                    continue
                    
                    # Check every 0.2 seconds
                    await asyncio.sleep(0.2)
                    
                except KeyboardInterrupt:
                    print("\n\n🛑 Engagement stopped by user")
                    break
                except Exception as loop_e:
                    print(f"❌ Loop error: {loop_e}")
                    await asyncio.sleep(2)
            
    except Exception as e:
        print(f"❌ Engagement mode error: {e}")
    finally:
        try:
            await browser.close()
        except:
            pass

async def main():
    parser = argparse.ArgumentParser(description="Instagram DM Auto Sender using Instagrapi")
    parser.add_argument('--username', required=True, help='Instagram username')
    parser.add_argument('--password', required=True, help='Instagram password')
    parser.add_argument('--thread-url', required=True, help='Full Instagram direct thread URL')
    parser.add_argument('--names', nargs='+', required=True, help='Messages list, direct string, or .txt file (split on & or "and" for multiple; preserves newlines for art)')
    parser.add_argument('--headless', default='true', choices=['true', 'false'], help='Run in headless mode (default: true)')
    parser.add_argument('--storage-state', required=True, help='Path to JSON file for login state (persists session)')
    parser.add_argument('--tabs', type=int, default=1, help='Number of parallel tabs per thread URL (1-5, default 1)')
    parser.add_argument('--rate', type=float, default=8.0, help='Messages per second target (default: 8.0)')
    parser.add_argument('--verify-window', type=float, default=0.1, help='Seconds to wait before verification (default: 0.1)')
    parser.add_argument('--safe-rate', type=float, default=4.0, help='Safe fallback messages per second when rate-limited (default: 4.0)')
    parser.add_argument('--min-rate', type=float, default=1.0, help='Minimum messages per second allowed (default: 1.0)')
    parser.add_argument('--failure-threshold', type=int, default=5, help='Number of rate errors within failure window to trigger safe mode (default: 5)')
    parser.add_argument('--failure-window', type=float, default=30.0, help='Seconds window to count failures (default: 30s)')
    parser.add_argument('--cooldown', type=float, default=60.0, help='Seconds to remain in safe mode once triggered (default: 60s)')
    args = parser.parse_args()
    args.names = sanitize_input(args.names)  # Handle bot/shell-truncated inputs

    thread_url = args.thread_url.strip()
    if not thread_url:
        print("Error: No valid thread URL provided.")
        return

    # Extract thread_id from URL
    thread_id = thread_url.split('/')[-1]
    if not thread_id.isdigit():
        print(f"Error: Invalid thread URL {thread_url}, extracted thread_id '{thread_id}' is not numeric.")
        return

    print(f"Extracted thread_id: {thread_id}")

    try:
        messages = parse_messages(args.names)
    except ValueError as e:
        print(f"Error parsing messages: {e}")
        return

    if not messages:
        print("Error: No valid messages provided.")
        return

    print(f"Parsed {len(messages)} messages.")

    # Login with Instagrapi
    cl = Client()
    session_file = args.storage_state.replace('_state.json', '_session.json')
    session_loaded = False
    
    if os.path.exists(session_file):
        try:
            cl.load_settings(session_file)
            print("Loaded existing session.")
            
            # Verify session is valid by checking if we can get user info
            try:
                user_info = cl.account_info()
                print(f"Session validated for user: {user_info.username}")
                session_loaded = True
            except Exception as verify_e:
                print(f"Session loaded but invalid: {verify_e}")
                session_loaded = False
                
        except Exception as e:
            print(f"Failed to load session: {e}")
            session_loaded = False

    # Only login if session wasn't loaded successfully
    if not session_loaded:
        try:
            cl.login(args.username, args.password)
            cl.dump_settings(session_file)
            print("Logged in successfully.")
        except Exception as e:
            print(f"Login failed: {e}")
            return
    else:
        print("Using existing session - skipping login.")

    # Start sending
    await sender_instagrapi(
        cl,
        thread_id,
        messages,
        rate=args.rate,
        verify_window=args.verify_window,
        safe_rate=args.safe_rate,
        min_rate=args.min_rate,
        failure_threshold=args.failure_threshold,
        failure_window=args.failure_window,
        cooldown=args.cooldown,
    )

if __name__ == "__main__":
    asyncio.run(main())