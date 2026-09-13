# Vendored Isabelle dependencies

`Regular-Sets` and `Abstract-Rewriting` are the AFP library snapshots bundled with the pinned Isabelle upstream repository. Their exact source paths and original hashes are recorded in [UPSTREAM.json](../../UPSTREAM.json).

They are included here because the application imports `Abstract-Rewriting.Abstract_Rewriting` for Newman's lemma, and that session depends on `Regular-Sets`. Retaining their session sources makes the build independent of a separate AFP checkout.

Authorship and copyright notices in all sources have been retained. The Abstract-Rewriting files include GNU LGPL notices, including LGPL version 3 or later in `Abstract_Rewriting.thy`. See the accompanying license texts in `LICENSES/`. Other source-specific notices remain authoritative. No application-wide license overrides those notices.
