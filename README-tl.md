# Confluence ng FREnv — Artifact para sa WCTP 2026

[English](README.md) | [日本語](README-ja.md) | Tagalog | [简体中文](README-zh.md)

Naglalaman ang repositoryong ito ng pormalisasyon sa Isabelle/HOL ng confluence ng buong beta/sigma reduction ng FREnv, kasama ang kaugnay na pormalisasyon sa Lean 4. Inihanda ito bilang artifact na kasama ng isang papel na isusumite sa WCTP 2026.

**Beripikasyon:** parehong matagumpay ang build sa Isabelle2025-2 at ang build at audit sa Lean 4.33.0 sa malilinis na GitHub Actions runner noong 2026-09-13. Tingnan ang [tala ng beripikasyon](docs/verification.md) para sa eksaktong commit na sinuri at sa mga log.

**Magkaiba ang antas ng pagkakumpleto ng dalawang pormalisasyon.** Nasa Isabelle ang teorema ng confluence para sa buong reduction at ang mga depensiya nito. Ang kinopyang pormalisasyon sa Lean ay may syntax, mga relation ng reduction, at napatunayang mga batayan para sa parallel reduction; **hindi pa nito napapatunayan ang confluence**. Ang matagumpay na Lean build ay nagpapatunay na tama ang mga deklarasyong naroon, hindi na nalutas na ang natitirang mga obligasyon sa patunay ng confluence.

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
  LambdaFrenv/          Mga depinisyon at napatunayang pantulong na lemma
  Audit.lean            Sinusuri ang mga deklarasyon at inililista ang mga axiom ng mga teorema
  docs/                 Mga espesipikasyon at natitirang obligasyon sa Ingles
  README.md             Mga tagubilin sa Lean build at eksaktong saklaw
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

Itinatakda ng kasamang `lean-toolchain` ang **leanprover/lean4:v4.33.0**. Ida-download ng Elan ang bersiyong iyon kung kailangan. Walang depensiya sa Mathlib at walang hakbang para sa pag-download ng cache. Tingnan ang [mga tagubilin para sa Lean](lean/README.md) para sa mga napatunayang deklarasyon at sa pagkakaiba ng pagde-depina ng isang proposisyon at pagpapatunay nito.

## Mga resulta at saklaw

| Pormalisasyon | Pangunahing nilalamang sinusuri | Confluence ng buong reduction ng FREnv |
|---|---|---|
| Isabelle/HOL | Confluence ng pantulong na calculus, translation, surjectivity, simulation, lifting, at ang panghuling teorema ng confluence | Naberipika sa naitalang session build na may aktibong pagsuri ng mga patunay |
| Lean 4 | Syntax na may mga constant, beta/sigma reduction, parallel reduction, congruence ng closure, embedding, at simulation | Walang patunay nito sa kinopyang rebisyon |

Magkaiba rin ang mga wikang pormal na ginagamit: string ang mga pangalan sa Isabelle at wala itong primitive constant; ginagawang mga type parameter ng Lean ang mga variable at constant. Hindi inaangkin ng artifact na ito na napatunayan ang equivalence ng dalawang encoding. Ipinaliliwanag ang mga pagkakaibang ito sa [mapa ng patunay](docs/proof-map.md).

Ipinaliliwanag ng mga matematikal na Markdown file ang daloy ng patunay, ngunit ang mismong mga tekstong iyon ay hindi machine-checked. Pinanatili ang mga sanggunian sa orihinal na tesis at roadmap upang masubaybayan ang pinagmulan; hindi kailangan ang PDF ng tesis upang patakbuhin ang alinman sa dalawang proof assistant.

## Reproducibility at pagkilala sa mga may-akda

Tingnan ang [PROVENANCE.md](PROVENANCE.md) para sa mga nakatakdang upstream revision at mga pagbabagong ginawa sa paghahanda ng artifact, ang [UPSTREAM.json](UPSTREAM.json) para sa talaan ng pinagmulan ng bawat file, at ang [docs/verification.md](docs/verification.md) para sa aktuwal na mga resulta ng beripikasyon. Inuulit ng dalawang GitHub Actions job ang mga build command sa malilinis na runner.

Pinanatili sa mga kasamang AFP source ang mga pahayag tungkol sa may-akda at lisensiya. Tingnan ang [paunawa para sa mga kasamang library](isabelle/vendor/README.md). Ang pagkopyang ito ay hindi nagbibigay ng bagong pangkalahatang lisensiya sa mga upstream na pormalisasyon.
