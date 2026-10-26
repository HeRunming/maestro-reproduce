"""Opt-in API connectivity probe. Never run implicitly by tests."""
import argparse
import asyncio
from pathlib import Path
from .agent import Budget, Session
from .config import Config


async def probe(config):
    session = Session(config.provider, 'Return exactly {"ok":true}.', Budget(config.provider.max_tokens))
    try:
        reply = await session.request('connectivity check', [])
        return reply.text.strip()
    finally:
        await session.close()


def main():
    parser = argparse.ArgumentParser(description='Make one real billable API request.')
    parser.add_argument('config', type=Path)
    parser.add_argument('--i-understand-this-costs-money', action='store_true', required=True)
    args = parser.parse_args()
    print(asyncio.run(probe(Config.load(args.config))))
