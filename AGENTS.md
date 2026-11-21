# LLM-Assisted Proving

Guidelines and prompts for using LLMs to write and refactor Lean 4 proofs in this repository.

## AGENTS.md hierarchy
- Agents form a DAG that mirrors the folder tree. An agent follows the `AGENTS.md` in its own folder **and** in every parent folder up to this root one; the nearest file wins on conflict.
- An agent whose folder has no `AGENTS.md` follows its nearest ancestor's, so it still inherits this file.
- A child file never restates a parent rule; it references the parent file instead.
- To formalize a mathematical statement from a pdf paper, handle it to [Lemma](Lemma/AGENTS.md) agent who will create a lemma path for this statement, visualize it with latex rendering via [vue](vue/AGENTS.md) agent and deploy via [mjs](mjs/AGENTS.md) agent using node.js .

## Sub-agents
- Work on https://github.com/math-proof/lemma.
- Grok bots may use a Remote Control Agent as Self-Hosted Worker on `main` (WSL `~/github/lean`), via [AgentName](https://cursor.com/agents/bc-UUID); never launch Cursor cloud agents unless deliberately demanded.
- Each agent is assigned a folder (agent name = folder name, e.g. Nat → `Lemma/Nat` or `Theorem/Nat`), and is subordinate to its parent agents, thus the hierarchy of agents form a Directed Acyclic Graph.
- To modify another folder, send the task to the agent named by that folder (see Inter-agent communication).
- If multiple colleague agents should work cooperatively, ask its parent agent for help. 
- If an agent required does not exist, ask the primary agent `md` for help.

## Inter-agent communication
- Inter-agent communication should forward necessary context to avoid misunderstanding.
This copy-paste path is for **Cursor-like** agents, who cannot talk to other agents. Do not claim you dispatched a job, and do not wait for a colleague that never receives the message.

**Grok** bots/Codex agents can talk to colleagues. They skip this section: send the job to @AgentName directly (do not give the user a paste prompt).

When the user says to send this issue / problem / bug / job / task to **@AgentName** (or “send to AgentName”):
- Write a **self-contained prompt** for that agent (assignee, goal, paths, errors, constraints, follow `AGENTS.md` within @AgentName folder or its parent folder if non-existent).
- Emit that prompt as **exactly one** fenced code block tagged `markdown` (opening line ` ```markdown `, closing ` ``` `). The chat UI must show **exactly one** clickable **copy** control for the whole prompt; the user clicks it instead of selecting text and pressing Ctrl+C.
- **One clickable only:** do not nest other fenced blocks (` ```… `) inside that prompt — each inner fence can add another copy button and the user cannot tell which to use. Put Lean/shell examples inside the prompt as indented plain text (or prose), never as nested triple-backtick fences.
- Never put the prompt in prose, a quote, a list, or several blocks — those have no one-click copy for the whole text.
- Prompt shape (first line and sections): open with
  `Assignee: AgentName (scope; this chat id <uuid>). Follow AGENTS.md; …`
  then `## Goal`, repro/paths/errors, constraints. Include the target agent **chat id** in Assignee when the user gave it (or when known).
- After the block, one short line telling the user to paste into that agent chat, naming the subagent as a markdown link:
  `[<path-or-scope> / AgentName](<chat-id>)`
  Example: `[lemmaPath / mjs](dfdec45a-5321-428c-9160-f3c47ec2af53)` — short scope or file path, then `/`, then the agent name; the link target is the agent **chat id** (UUID). Prefer this over bare `@AgentName` when a chat id is available.

## Edit Privilege
- Scratch/temp files (probes, bisect scripts, ad-hoc `tmp_*` / `probe_*` / `test_*` files) live in the gitignored `tmp/` folder, not at the repo root.
- Stay on `main`. Do not switch to any other branch; merge changes into `main` instead.
- Never edit `lean-toolchain` or `lakefile.toml` manually.
