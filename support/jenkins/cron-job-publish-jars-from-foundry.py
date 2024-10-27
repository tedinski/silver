#!/usr/bin/env python3

# This runs on coldpress (or any other machine with UMN NFS).
#
# */10 * * * * /lhome/gitbot/cron-job-publish-jars-from-foundry.py
#
# Note that this currently does not self-update, or check for timestamps (it
# uses hashes instead).

import json
from os import environ, listdir, remove
from os.path import exists, isdir, isfile, join
from shutil import copyfile, rmtree
from subprocess import check_call, check_output
import sys
from tempfile import TemporaryDirectory, TemporaryFile
from urllib.request import Request, urlopen

WEB_STORE = environ.get("WEB_STORE", "/web/research/melt.cs.umn.edu")
SLACK_WEBHOOK_URL = environ.get("SLACK_WEBHOOK_URL", None)

dont_delete = ["copper", "downloads", "melt-artifacts"]

files = [
    "CopperCompiler.jar",
    "CopperRuntime.jar",
    "commonmark-0.17.1.jar",
    "edu.umn.cs.melt.exts.silver.ableC.composed.with_ableC.jar",
    "edu.umn.cs.melt.exts.silver.ableC.composed.with_all.jar",
    "edu.umn.cs.melt.exts.silver.ableC.composed.with_base.jar",
    "silver-latest.tar.gz",
    "silver.core.jar",
    "silver.util.jar",
    "silver.langutil.jar",
    "silver.rewrite.jar",
    "silver.regex.jar",
    "silver.compiler.composed.Default.jar",
    "silver-langserver-launcher.jar",
    "silverlsp-latest.vsix",
    "website.tar.gz",
]

if SLACK_WEBHOOK_URL is None:
    try:
        with open(
            "/lhome/gitbot/cron-job-publish-jars-from-foundry-slack-webhook-url.txt"
        ) as f:
            # To recreate this file:
            #
            # 1. Be a collaborator on the corresponding Slack app.
            # 2. Go to https://api.slack.com/apps/A01F6CM5X46/install-on-team?
            # 3. SSH to coldpress
            # 4. sudo -u gitbot vim /lhome/gitbot/cron-job-publish-jars-from-foundry-slack-webhook-url.txt
            # 5. Hit Copy on the appropriate webhook from the Slack page from step 2
            # 6. Paste it into the file
            # 7. Google how to exit Vim
            SLACK_WEBHOOK_URL = f.read().strip()
    except:
        pass


def send_to_slack(fmt, *args):
    if SLACK_WEBHOOK_URL is None:
        print(fmt.format(*args), file=sys.stderr)
    else:
        urlopen(
            Request(
                SLACK_WEBHOOK_URL,
                data=json.dumps({"text": fmt.format(*args)}).encode("utf-8"),
                headers={"Content-type": "application/json"},
            )
        )


def download_new_files(kont):
    """
    Downloads new files and calls kont with the directory the files are
    downloaded to.
    """
    old_hashes = None
    try:
        with open(join(WEB_STORE, "downloads/silver-dev/jars/SHA256SUMS"), "rb") as f:
            old_hashes = f.read()
    except Exception:
        pass
    with TemporaryDirectory() as download_dir:
        for name in files:
            with open(join(download_dir, name), "wb") as f:
                resp = urlopen("https://foundry.remexre.xyz/custom-stable-dump/" + name)
                f.write(resp.read())

        # Compute the new hashes. This lets us skip the whole extraction
        # process if the files didn't really change, which saves some work and
        # lets us avoid constant blips of downtime every 10 minutes.
        hashes = check_output(["sha256sum"] + files, cwd=download_dir)
        with open(join(download_dir, "SHA256SUMS"), "wb") as f:
            f.write(hashes)

        if old_hashes != hashes:
            return kont(download_dir)


def install(download_dir):
    """
    Installs the website and jars, which are expected to be downloaded to download_dir.

    Returns a list of errors that occurred.
    """

    errors = []

    def onerror(*args):
        print(*args)
        errors.append(args)

    # Delete the old files.
    for f in listdir(WEB_STORE):
        if f in dont_delete:
            continue
        f = join(WEB_STORE, f)
        if isdir(f):
            rmtree(f, onerror=onerror)
        elif isfile(f):
            remove(f)
        else:
            onerror(f + " is neither a directory or a file")

    # Untar the new website in.
    # --no-overwrite-dir and --touch are required (for now?) because the
    # permissions on all the dont_delete dirs are such that we can't write to
    # them...
    check_call(
        [
            "tar",
            "--no-overwrite-dir",
            "--touch",
            "-zxf",
            join(download_dir, "website.tar.gz"),
            "-C",
            WEB_STORE,
        ]
    )

    # Copy the rest of the files (the JARs) into the jars directory.
    for f in listdir(download_dir):
        copyfile(join(download_dir, f), join(WEB_STORE, "downloads/silver-dev/jars", f))

    # Fix up permissions.
    check_call(
        ["find", "-type", "d", "-exec", "chmod", "775", "{}", ";"], cwd=WEB_STORE
    )
    check_call(
        ["find", "-type", "d", "-exec", "chmod", "g+s", "{}", ";"], cwd=WEB_STORE
    )
    check_call(
        ["find", "-type", "f", "-exec", "chmod", "664", "{}", ";"], cwd=WEB_STORE
    )

    return errors


try:
    errors = download_new_files(install)
    if errors is None:
        pass
    elif len(errors) == 0:
        send_to_slack("Deployed new jars/website!")
    else:
        send_to_slack("Deployed new jars/website with errors: `{}`", errors)
except Exception as e:
    send_to_slack("Caught exception `{}`", e)
