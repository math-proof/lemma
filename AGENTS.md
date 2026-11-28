# LLM-Assisted Proving

Guidelines and prompts for using LLMs to write and refactor Lean 4 proofs in this repository.

## AGENTS.md hierarchy
- Agents form a DAG that mirrors the folder tree. An agent follows the `AGENTS.md` in its own folder **and** in every parent folder up to this root one; the nearest file wins on conflict.
- An agent whose folder has no `AGENTS.md` follows its nearest ancestor's, so it still inherits this file.
- A child file never restates a parent rule; it references the parent file instead.
- To formalize a mathematical statement described in natural language, handle the informal content to [Lemma](Lemma/AGENTS.md) agent who will create a lemma path for this statement, visualize it with latex rendering via [vue](vue/AGENTS.md) agent and deploy via [mjs](mjs/AGENTS.md) agent using node.js .

## Sub-agents
- Work on https://github.com/math-proof/lemma.
- Each agent is assigned a folder (agent name = folder name, e.g. Nat → `Lemma/Nat` or `Theorem/Nat`), and is subordinate to its parent agents, thus the hierarchy of agents form a Directed Acyclic Graph.
- To modify another folder, send the task to the agent named by that folder (see Inter-agent communication).
- If multiple colleague agents should work cooperatively, ask its parent agent for help. 
- If an agent required does not exist, ask the primary agent `md` for help.

## Inter-agent communication
- Inter-agent communication should forward necessary context to avoid misunderstanding.
- Grok and Codex deliver every message themselves. The programmer is not a courier: do not print a paste prompt, a fenced copy block, or ask anyone to copy text between chats.

### Instruction (A → B)
A hands a one-shot task to B. Triggered when the user says "send this issue / problem / bug / job / task to **@AgentName**" (or "send to AgentName"), or when A's work must change B's folder.
- Write a **self-contained prompt** as one clickable to copy (assignee, goal, paths, errors, constraints; follow `AGENTS.md` in @AgentName's folder, or the nearest parent `AGENTS.md` if that folder has none). Put Lean and shell examples in the prompt as indented plain text.
- Prompt shape: open with
  `Assignee: AgentName ($scope). Follow the nearest AGENTS.md; If you want to modify a file beyond $scope, send a prompt to the corresponding folder agent to whom I will paste…`
  then `## Goal`, repro/paths/errors, constraints.
- Then tell the user, in one short line, who has the task. Link the worker `[<scope> / AgentName](<subagent-id>)` with the id the channel returned.
- If delivery fails, report the error. Do not fall back to a paste block.

### Conversation (A ⇄ B)
Follow-ups use the same channel. `Assignee:` starts a task. `To:` names the recipient of a reply so that agent resumes from the previous turn.

Returning a report (A ← B): when B finishes A's task, B sends the report back to A on that channel.
- Open with
  `To: AgentA (scope). From: AgentB. Report on task: <one-line summary>`
  then `## Result` (what changed — files, build/lint status), `## Suggested Decision` (choices made / open questions).
- A continues from that report. The programmer does not paste it.

## Edit Privilege
- Scratch/temp files (probes, bisect scripts, ad-hoc `tmp_*` / `probe_*` / `test_*` files) live in the gitignored `tmp/` folder, not at the repo root.
- Stay on `main`. Do not switch to any other branch; merge changes into `main` instead.
- Never edit `lean-toolchain` or `lakefile.toml` manually.
