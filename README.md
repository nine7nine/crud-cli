# crud-cli

A fast [notcurses](https://github.com/dankamongmen/notcurses) terminal front-end for the official
**Claude Code** CLI. It drives `claude` in headless streaming mode and renders a rich, flicker-free
TUI: streaming markdown, syntax-highlighted diffs, slash commands, `@`-file mentions, inline images,
mouse selection, vim editing, and session resume/rename.

> Unofficial, third-party project — not affiliated with or endorsed by Anthropic. It uses your
> existing Claude Code installation through the official `claude` CLI.

## Requirements

- The official **`claude`** CLI on your `PATH` (or point at it with `--claude-bin` / `$CRUD_CLAUDE_BIN`)
- **notcurses** (core) with headers — resolved via `pkg-config` as `notcurses-core`
- A C compiler, `make`, `pkg-config`, and pthreads

## Build

```sh
make            # release build  → ./crud-cli
make asan       # ASan/UBSan build → ./crud-cli-asan
```

## Install

```sh
sudo make install PREFIX=/usr     # → /usr/bin/crud-cli
```

## Usage

```sh
crud-cli [options] [prompt]
```

Run it from the directory you want Claude to work in. A positional `prompt` is sent as the first
message on launch.

| Flag | Description |
| --- | --- |
| `-c`, `--continue` | resume the most recent session in this directory |
| `-r`, `--resume [name\|id]` | resume a session by name/id (no arg: pick from a list) |
| `-n`, `--name <name>` | name this session (shown in the resume picker) |
| `--model <m>` | model alias (`opus`, `sonnet`, `haiku`, …) |
| `--effort <level>` | `low` · `medium` · `high` · `xhigh` · `max` |
| `--permission-mode <m>` | `default` · `acceptEdits` · `plan` · `bypassPermissions` |
| `--add-dir <dirs...>` | extra directories the engine may access |
| `--agent <agent>` | session agent |
| `--claude-bin <path>` | engine binary (else `$CRUD_CLAUDE_BIN`, else `claude`) |

## In-session

- `/` slash commands — `/model` `/effort` `/resume` `/rename` `/usage` `/context` `/diff` `/export`
  `/cost` `/plan` `/clear` and more; type `/help` for the full list
- `@` to mention files · `!cmd` to run a shell command · `#note` to append to `CLAUDE.md`
- Multi-line input, history (↑/↓), reverse-search (`Ctrl+R`), vim mode (`/vim`)
- Mouse: drag to select, `Ctrl+C` to copy, wheel to scroll
- `Shift+Tab` cycles permission mode · `Ctrl+O` expand/collapse tool output · `Ctrl+V` paste an image
- `Ctrl+C` backs out of the draft / stops the current turn; on an empty prompt it confirms before exiting

## License

[MIT](LICENSE)
