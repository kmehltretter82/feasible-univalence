# LogrelMLTT — logical-relation development with Σ, Unit, Empty (and Id)

Work in progress on branch `logrel-ext`. Standalone Lake package (`lean_lib LogrelMLTT`,
toolchain `leanprover/lean4:v4.33.1`, no dependencies) extending the Lean port of
Abel, Öhman, Vezzosi, *Decidability of Conversion for Type Theory in Type Theory* (POPL 2018)
in `../abel2018/Abel2018` with the type formers of the later
[logrel-mltt](https://github.com/mr-ohman/logrel-mltt) development.

The initial commit is a verbatim copy of the 14 `Abel2018` modules with the namespace renamed
to `LogrelMLTT`; subsequent commits extend them. See the final README section for sources and
deviations.
