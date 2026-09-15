# Verifying the Mizar development

Everything needed to re-check the proof is in this `mizar/` directory. No
library beyond the standard MML is used, and nothing is downloaded during
verification.

## 1. Install Mizar

Get the Mizar system from the
[official download page](https://mizar.uwb.edu.pl/system/) and follow its
installation instructions. The development was checked with

```text
Mizar Ver. 8.1.15 (Linux/FPC)
MML 5.99, 1507 articles
```

Any recent Mizar release whose MML still contains `REWRITE1`, `DTCONSTR`,
`TREES_1`–`TREES_4` and `LANG1` should work; those are long-standing articles.

Two things must be right afterwards.

**`PATH`.** The commands `mizf`, `verifier`, `accom`, `makeenv` and `miz2prel`
must be callable. The Linux distribution installs them into `/usr/local/bin`.

```sh
command -v mizf verifier accom makeenv miz2prel
```

**`MIZFILES`.** It must name the Mizar library directory — the one that
contains `mml/`, `prel/`, `mml.ini` and `mizar.msg`. The Linux distribution
installs it at `/usr/local/share/mizar`.

```sh
export MIZFILES=/usr/local/share/mizar
ls "$MIZFILES"          # expect: abstr mml mml.ini mizar.msg prel ...
verifier                # prints the version banner, then complains about
                        # an empty parameter list; that is expected
```

The installer normally adds `MIZFILES` to your shell profile. A non-interactive
shell may not read that profile, so export it explicitly as above, or let
`verify.sh` fall back to its default.

Platform notes: on Windows use the Mizar Windows distribution and run the
commands from a shell that provides `sh` (Git Bash or MSYS), or install the
Linux distribution inside WSL and work entirely inside WSL. Do not mix a
Windows Mizar binary with a WSL shell.

## 2. Obtain the sources

```sh
git clone https://github.com/nisizaki/frenv-confluence-WCTP.git
cd frenv-confluence-WCTP/mizar
```

Record the commit hash with `git rev-parse HEAD` when citing a particular
revision.

## 3. Verify everything

```sh
./verify.sh
```

Expected output:

```text
enveps_1   ok
enveps_2   ok
enveps_3   ok
enveps_4   ok
enveps_5   ok
enveps_6   ok
enveps_7   ok
enveps_8   ok
enveps_9   ok
frenv_1    ok
frenv_2    ok
frenv_3    ok
frenv_4    ok
frenv_5    ok
audit      ok

All 14 articles verified with no errors, and the audit article
re-derives each main result from its citation alone.
Main theorem: FRENV_5:8  (FrRed(V) is confluent)
```

The script exits with status 0 on success and 1 on the first failure, printing
the failing article's error file. A full run takes roughly a minute and a half.

What it does, for each article in turn:

1. `mizf text/<article>.miz` — runs the accommodator and the verifier. The
   accommodator reads the environment declarations at the top of the article
   and imports the MML items it names, plus the items of the earlier articles
   of this development from the local `prel/`. The verifier then checks every
   inference.
2. If `text/<article>.err` is non-empty, stop and report.
3. `miz2prel text/<article>.miz` — exports the article's definitions, theorems,
   schemes, registrations and clusters into `prel/`, so the later articles can
   import it.

The order matters: each article imports the ones before it. `verify.sh` uses
the correct order.

Finally it checks `text/audit.miz`, described in section 6. That article is a
leaf — nothing imports it — so it is not exported to `prel/`.

To start from a clean state:

```sh
./verify.sh clean    # removes prel/ and every generated file under text/
```

## 4. Reading the result

**Mizar has no `sorry`.** There is no mechanism for admitting a goal, no
axiom-introduction command available to an ordinary article, and no way to mark
a proof as incomplete. Every article here ends with an empty `.err` file, which
means the verifier accepted every inference step in it.

An error file is a list of lines

```text
<line> <column> <error-code>
```

Look the code up in the message catalogue:

```sh
grep -A1 '^# 4$' "$MIZFILES/mizar.msg"
```

`mizf` also writes the error positions back into the `.miz` file as comment
lines starting with `::>`, directly under the offending line. Those comments
are removed the next time the article verifies cleanly. The sources in this
repository contain no `::>` lines.

There is nothing corresponding to the Lean development's axiom audit, because
a Mizar article cannot introduce an axiom. The only things an article may
assume are the environment items it declares, and those are resolved by the
accommodator against the MML and the local `prel/`. What can still go wrong is
that a citation does not say what a reader thinks it says; `text/audit.miz`,
described next, is the check against that.

## 5. Checking one article

After the articles it depends on have been exported to `prel/`:

```sh
./check.sh enveps_8
```

This runs `mizf` on that article alone and prints its error file. Use it when
editing. It does not re-export to `prel/`; run `./verify.sh` for that.

## 6. Inspecting the statements

The articles are plain text and are meant to be read. The main results are at
the end of the last article:

```sh
sed -n '/^theorem Th8:/,/^end;/p' text/frenv_5.miz     # FRENV_5:8
sed -n '/^theorem Th6:/,/^proof/p'  text/frenv_5.miz   # FRENV_5:6
```

Theorem numbering inside an article is positional: the *n*-th `theorem` of
article `FOO` is cited as `FOO:n`, and the labels `Th1`, `Th2`, … used in the
sources follow that numbering. A definition labelled `:DefN:` is cited as
`FOO:def N`.

To confirm that a citation means what a reader thinks it means, the honest
check is to make a separate article depend on it: restate the claim and justify
it by the citation alone. `text/audit.miz` does exactly that for the six main
results, and `verify.sh` checks it. Its body is

```text
theorem
  SigmaRed(V) is strongly-normalizing by ENVEPS_1:43;

theorem
  SigmaRed(V) is confluent by ENVEPS_4:12;

theorem
  BetaRed(V) is confluent by ENVEPS_7:34;

theorem
  BetaSigmaRed(V) is confluent by ENVEPS_9:13;

theorem
  FrRed(V) is confluent by FRENV_5:8;

theorem
  for P,Q1,Q2 being FrEnvTerm of V
  st FrRed(V) reduces P,Q1 & FrRed(V) reduces P,Q2
  ex Q being FrEnvTerm of V st
    FrRed(V) reduces Q1,Q & FrRed(V) reduces Q2,Q
  by FRENV_5:6;
```

Each statement is written out in full here and is accepted only because the
cited theorem really has that content; a deliberately altered variant is
rejected with error code 4, "This inference is not accepted". Editing
`text/audit.miz` and re-running `./check.sh audit` is a cheap way to probe what
any of the results actually say.

## 7. Troubleshooting

| Symptom | Cause |
|---|---|
| `**** Can't open ' .../mml.ini '` | `MIZFILES` is unset or wrong. |
| Error 8xx on the environment lines | The accommodator could not find an imported article. Run `./verify.sh` from this directory so that `prel/` and `dict/` are found; the earlier articles must have been exported first. |
| Error 203 on a citation like `ENVEPS_1:17` | The cited article is not listed in the `theorems` directive of the citing article. (`definitions` is only for automatic unfolding.) |
| Error 200 | A line longer than 80 characters. Mizar enforces that limit. |
| Stale or inconsistent results after editing | `./verify.sh clean`, then `./verify.sh`. |
| Verification passes but you changed nothing | That is the expected steady state; `mizf` re-checks from scratch every time, there is no caching. |

## 8. Recorded verification

| | |
|---|---|
| Date | 2026-09-15 |
| System | Mizar Ver. 8.1.15 (Linux/FPC), MML 5.99 |
| Platform | Ubuntu on WSL 2 |
| Command | `./verify.sh` from a clean checkout |
| Result | 14 articles plus the audit article, every `.err` file empty, `FRENV_5:8` established |
| Wall clock | about 91 seconds |

Unlike the Isabelle and Lean developments in this artifact, the Mizar
development is not re-checked by a GitHub Actions job: there is no packaged
Mizar distribution that a clean runner can install without a manual download
step.
