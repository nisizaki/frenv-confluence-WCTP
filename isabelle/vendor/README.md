# Vendored Isabelle dependencies

`Regular-Sets` and `Abstract-Rewriting` are the AFP library snapshots bundled with the pinned Isabelle upstream repository. Their exact source paths and original hashes are recorded in [UPSTREAM.json](../../UPSTREAM.json).

They are included here because the application imports `Abstract-Rewriting.Abstract_Rewriting` for Newman's lemma, and that session depends on `Regular-Sets`. Retaining their session sources makes the build independent of a separate AFP checkout.

Authorship and copyright notices in all sources have been retained. The Abstract-Rewriting files include GNU LGPL notices, including LGPL version 3 or later in `Abstract_Rewriting.thy`. See the accompanying license texts in `LICENSES/`. Other source-specific notices remain authoritative. No application-wide license overrides those notices.

The [Regular-Sets entry](https://isa-afp.org/entries/Regular-Sets.html) is distributed under the AFP BSD license, whose text is included as [LICENSES/AFP-BSD.txt](LICENSES/AFP-BSD.txt). The [Abstract-Rewriting entry](https://isa-afp.org/entries/Abstract-Rewriting.html) identifies its LGPL license; [LICENSES/LGPL-3.0.txt](LICENSES/LGPL-3.0.txt) and [LICENSES/GPL-3.0.txt](LICENSES/GPL-3.0.txt) provide the corresponding GNU license texts.
