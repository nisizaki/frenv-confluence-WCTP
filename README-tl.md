# Confluence ng FREnv — Artifact para sa WCTP 2026

[English](README.md) | [日本語](README-ja.md) | Tagalog | [简体中文](README-zh.md)

Naglalaman ang repositoryong ito ng pormalisasyon sa Isabelle/HOL ng confluence ng buong beta/sigma reduction ng FREnv, kasama ang kaugnay na mga pormalisasyon sa Lean 4 at Mizar. Inihanda ito bilang artifact na kasama ng isang papel na isusumite sa WCTP 2026.

**Beripikasyon:** parehong matagumpay ang build sa Isabelle2025-2 at ang build at audit sa Lean 4.33.0 sa malilinis na GitHub Actions runner noong 2026-09-13, sa commit `725b0b6`, ang rebisyong naglalaman ng patunay ng confluence sa Lean. Tingnan ang [tala ng beripikasyon](docs/verification.md) para sa eksaktong mga commit na sinuri at sa mga log.

**Napapatunayan na ng tatlong pormalisasyon ang buong confluence, sa magkakahiwalay na paraan.** Nasa Isabelle ang teorema ng confluence para sa buong reduction at ang mga depensiya nito. Pinapatunayan din ng pormalisasyon sa Lean ang parehong pahayag para sa sarili nitong encoding, bilang `LambdaFrenv.frenv_beta_sigma_confluent`, at ng pormalisasyon sa Mizar bilang `FRENV_5:8`. Pareho ang ruta ng tatlo (pantulong na calculus, sigma normalization, beta over sigma, translation) ngunit may sariling mga depinisyon at patunay ang bawat isa. Nananatiling magkaiba ang mga encoding — may primitive constants type ang Lean, at magkaiba ang pagtrato nila sa mga variable — at hindi inaangkin ng artifact na ito na napatunayan ang equivalence ng mga ito.

## Estruktura ng mga direktoryo

```text
isabelle/
  ROOTS                 Nagrerehistro ng apat na session na may kumpletong source
  FREnv/                Syntax, reduction, at local confluence ng FREnv
  EnvEps/               Pantulong na calculus at paglilipat ng full confluence
  vendor/               Kailangang AFP source: Regular-Sets at Abstract-Rewriting
  docs/                 Mga paliwanag sa matematika sa Ingles
  README.md             Mga tagubilin sa Isabelle build at interaktibong pagsusuri
lean/
  lean-toolchain        Nakatakdang bersiyon ng Lean
  lakefile.toml         Konpigurasyon ng Lake project
  lake-manifest.json    Manifest ng mga depensiya (walang panlabas na package)
  LambdaFrenv.lean       Pangunahing entry point ng library
  LambdaFrenv/          Mga depinisyon at patunay, kasama ang teorema ng confluence
  LambdaFrenv/EnvEps/   Ang pantulong na calculus at ang patunay ng confluence nito
  Audit.lean            Sinusuri ang mga deklarasyon at inililista ang mga axiom ng mga teorema
  docs/                 Mga espesipikasyon ng syntax at reduction sa Ingles
  README.md             Mga tagubilin sa Lean build, estruktura, at daloy ng patunay
mizar/
  text/                 Ang labinlimang artikulo, at ang artikulong pang-audit
  dict/                 Mga pribadong vocabulary para sa mga simbolong idinagdag dito
  verify.sh             Nagbeberipika ng lahat ng artikulo ayon sa pagkakasunod
  check.sh              Nagbeberipika ng isang artikulo
  docs/                 Mga tagubilin sa beripikasyon at mga tala ng gawain
  README.md             Mga kailangan sa Mizar, estruktura, at daloy ng patunay
docs/
  proof-map.md          Pangunahing resulta, daloy ng mga depensiya, at mga pagkakaiba
  verification.md       Tala ng beripikasyon
UPSTREAM.json           Eksaktong source commit at hash ng mga orihinal na file
PROVENANCE.md           Saklaw ng kinopya at mga pagbabago sa paghahanda ng artifact
.github/workflows/      Magkahiwalay na verification job para sa Isabelle at Lean
```

## Pagkuha ng artifact

```sh
git clone https://github.com/nisizaki/frenv-confluence-WCTP.git
cd frenv-confluence-WCTP
git rev-parse HEAD
```

Itala ang buong commit hash kapag sinisipi o sinusuri ang artifact. Gamitin ang `git checkout <commit-hash>` upang maibalik ang isang partikular na rebisyon. Hindi kailangan ang mga submodule o ang mga orihinal na repositoryo upang i-build ang checkout na ito.

## Beripikasyon sa Isabelle/HOL

I-install ang **Isabelle2025-2** na angkop sa iyong platform mula sa [opisyal na pahina ng pag-install](https://isabelle.in.tum.de/installation.html). Idagdag ang direktoryong `bin` nito sa iyong `PATH`, at patakbuhin ang sumusunod mula sa root directory ng repositoryong ito:

```sh
isabelle version
isabelle build -v -j 1 -o threads=2 -o quick_and_dirty=false -D isabelle
```

Binubuo nito ang mga kasamang AFP dependency, ang session na `FREnv`, at ang session na `EnvEps` na naglalaman ng panghuling resulta:

```text
FREnv_Full_Confluence_Via_Translation.frenv_beta_sigma_confluent
```

Isinasaad ng resultang ito na ang mga dulo ng alinmang dalawang finite na sunod-sunod na beta/sigma reduction mula sa iisang FREnv term ay maaaring ma-reduce sa isang karaniwang term. Tingnan ang [mga tagubilin para sa Isabelle](isabelle/README.md) para sa mga detalye ayon sa platform at sa interaktibong pagsusuri. Aktibo ang pagsuri ng mga patunay: tahasang hindi pinapagana ng artifact ang `quick_and_dirty`.

## Beripikasyon sa Lean 4

I-install ang [Elan](https://lean-lang.org/install/manual/), ang tagapamahala ng Lean toolchain, at tiyaking maaaring patakbuhin ang `lake` mula sa iyong `PATH`. Pagkatapos, patakbuhin ang:

```sh
cd lean
lake env lean --version
lake build
lake env lean Audit.lean
```

Itinatakda ng kasamang `lean-toolchain` ang **leanprover/lean4:v4.33.0**. Ida-download ng Elan ang bersiyong iyon kung kailangan. Walang depensiya sa Mathlib at walang hakbang para sa pag-download ng cache. Itinatatag ng build na ito ang

```text
LambdaFrenv.frenv_beta_sigma_confluent
```

na siyang katumbas sa Lean ng teorema sa Isabelle. Tingnan ang [mga tagubilin para sa Lean](lean/README.md) para sa estruktura ng mga module at sa daloy ng patunay.

## Beripikasyon sa Mizar

I-install ang **Mizar Ver. 8.1.15** at ang MML nito mula sa [pahina ng pag-download ng Mizar](https://mizar.uwb.edu.pl/system/), ilagay ang mga executable nito sa `PATH`, at itakda ang `MIZFILES` sa direktoryo ng aklatan ng Mizar. Pagkatapos ay patakbuhin ang:

```sh
cd mizar
export MIZFILES=/usr/local/share/mizar   # kung hindi pa ito itinakda ng installer
./verify.sh
```

Binebalida nito ang labinlimang artikulo ayon sa pagkakasunod ng depensiya, ini-export ang bawat isa sa lokal na `prel/` upang mai-import ito ng susunod, at sa huli ay sinusuri ang isang artikulong pang-audit na inuulit ang bawat pangunahing resulta at pinatutunayan ito sa pamamagitan lamang ng sipi nito. Walang ginagamit na aklatan maliban sa karaniwang MML at walang dina-download habang nagbeberipika. Itinatatag ng build ang

```text
FRENV_5:8   for V being non empty set holds FrRed(V) is confluent
```

na siyang katumbas sa Mizar ng mga teorema sa Isabelle at Lean. Walang `sorry` sa Mizar at walang paraan para magpasok ng axiom ang isang artikulo, kaya ang walang lamang `.err` na file ay nangangahulugang nasuri ang bawat inference. Tingnan ang [mga tagubilin para sa Mizar](mizar/README.md) para sa estruktura at sa daloy ng patunay, at ang [gabay sa beripikasyon](mizar/docs/verification.md) para sa kahulugan ng output at kung paano suriin ang bawat resulta.

## Mga resulta at saklaw

| Pormalisasyon | Pangunahing nilalamang sinusuri | Confluence ng buong reduction ng FREnv |
|---|---|---|
| Isabelle/HOL | Confluence ng pantulong na calculus, translation, surjectivity, simulation, lifting, at ang panghuling teorema ng confluence | Naberipika sa naitalang session build na may aktibong pagsuri ng mga patunay |
| Lean 4 | Abstract rewriting at lemma ni Newman, ang pantulong na calculus, termination at confluence ng sigma, mga sigma-normal form, diamond property ng parallel beta, composition compatibility, translation at lifting | Naberipika sa naitalang Lean build |
| Mizar | Estruktura ng dalawang calculus bilang parse tree, termination at confluence ng sigma sa pamamagitan ng lemma ni Newman mula sa MML, mga sigma-normal form, triangle property ng parallel beta, composition compatibility, paraang interpretation ni Hardin, translation at lifting | Naberipika sa pamamagitan ng `mizar/verify.sh` |

Magkaiba rin ang mga wikang pormal na ginagamit: string ang mga pangalan sa Isabelle at wala itong primitive constant; ginagawang mga type parameter ng Lean ang mga variable at constant; ang Mizar naman ay may parameter na isang arbitraryong hindi walang laman na set ng mga variable at, tulad ng Isabelle, walang constant. Hindi inaangkin ng artifact na ito na napatunayan ang equivalence ng tatlong encoding. Ipinaliliwanag ang mga pagkakaibang ito sa [mapa ng patunay](docs/proof-map.md).

Ipinaliliwanag ng mga matematikal na Markdown file ang daloy ng patunay, ngunit ang mismong mga tekstong iyon ay hindi machine-checked. Pinanatili ang mga sanggunian sa orihinal na tesis at roadmap upang masubaybayan ang pinagmulan; hindi kailangan ang PDF ng tesis upang patakbuhin ang alinman sa dalawang proof assistant.

## Reproducibility at pagkilala sa mga may-akda

Tingnan ang [PROVENANCE.md](PROVENANCE.md) para sa mga nakatakdang upstream revision at mga pagbabagong ginawa sa paghahanda ng artifact, ang [UPSTREAM.json](UPSTREAM.json) para sa talaan ng pinagmulan ng bawat file, at ang [docs/verification.md](docs/verification.md) para sa aktuwal na mga resulta ng beripikasyon. Inuulit ng dalawang GitHub Actions job ang mga build command sa malilinis na runner.

Pinanatili sa mga kasamang AFP source ang mga pahayag tungkol sa may-akda at lisensiya. Tingnan ang [paunawa para sa mga kasamang library](isabelle/vendor/README.md). Ang pagkopyang ito ay hindi nagbibigay ng bagong pangkalahatang lisensiya sa mga upstream na pormalisasyon.
