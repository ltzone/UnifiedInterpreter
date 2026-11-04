"""Validate the port with a real local Rocq MCP server (requires MCP Python SDK).
Run after the native dependency build. ROCQ_MCP selects the server executable.
This is an MCP client; it never invokes coqc/rocqtop itself.
"""
import asyncio
import json
import os
from pathlib import Path
from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import stdio_client

async def main():
    root = Path(__file__).resolve().parent.parent / 'rocq'
    params = StdioServerParameters(
        command=os.environ.get('ROCQ_MCP', 'rocq-mcp'),
        env=dict(os.environ, ROCQ_DUNE_BUILD='0'))
    async with stdio_client(params) as (read, write):
        async with ClientSession(read, write) as session:
            await session.initialize()
            async def call(tool, **args):
                reply = await session.call_tool(tool, args)
                result = reply.structuredContent or json.loads(reply.content[0].text)
                print(json.dumps({'tool': tool, 'args': args, 'result': result}), flush=True)
                if reply.isError or not result.get('success'):
                    raise RuntimeError(f'{tool} failed')
                return result
            await call('rocq_health')
            for name in ['Memory', 'MemoryProof', 'Syntax', 'Operations', 'Denotation', 'ProgramProof']:
                await call('rocq_compile_file', file=f'Sequential/{name}.v',
                           workspace=str(root), keep_vo=True, mode='full', include_warnings=False)
            for file, theorem in [('MemoryProof', 'embed_preserves_memory'),
                                  ('ProgramProof', 'allocate_binds_ssa')]:
                result = await call('rocq_assumptions', file=f'Sequential/{file}.v',
                                    name=theorem, workspace=str(root), timeout=120)
                if result.get('assumptions'):
                    raise RuntimeError(f'Unexpected assumptions: {theorem}')

if __name__ == '__main__':
    asyncio.run(main())
