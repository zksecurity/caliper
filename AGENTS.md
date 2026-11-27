# Agents

The commit convention for this repository. It applies to commits only.

## Commits

Commit messages follow [Conventional Commits](https://www.conventionalcommits.org):

```
<type>(<scope>): <description>

<body>
```

- **Type**: one of `feat`, `fix`, `refactor`, `test`, `docs`, `chore`, `perf`, `style`, `ci`,
  `build`.
- **Scope** (optional): the part of the library touched, in lower case, for example `core`,
  `witgen`, `rv64`, `readme`, `assets`.
- **Description**: imperative mood ("add", not "added"), lower case, no final period, and a
  subject line of at most 50 characters.
- **Body** (optional): separated by a blank line, wrapped at 72 characters. Say what changed
  and why, not how.
- One logical change per commit.
- Sign every commit (`git commit -S`).
- No AI attribution: never mention Claude or another AI assistant, and add no
  `Co-Authored-By` trailer for one.
  Claude is a tool: you would not co-author with your editor, OS, window manager or Herman
  Miller chair. You are responsible for the code you commit.
- Merge pull requests without squashing, so their commits land as written. Squash only a very
  small pull request, or one whose history went back and forth into a mess; the squash commit
  then follows the convention too, so write its message rather than keeping the pull request
  title.
- When a maintainer rewrites a contributor's commit (for example, to fix its message), the
  contributor stays the author and the maintainer is the committer.

Examples:

```
refactor: rename terminationTime to runTime
docs(readme): reword the opening line
build: port to Lean 4.36 and Mathlib v4.36.0
```
