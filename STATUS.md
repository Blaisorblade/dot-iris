
# List of the semantic typing lemmas, and their status in Coq.

The names are taken from the PDF. In parens, you'll find the names of lemmas.

## Structural typing lemmas

- [ ] T-Weak

- [ ] <:-Weak

- [x] T-Sub (T_Sub)

- [x] T-Var (T_Var)

- [x] <:-Refl (Sub_Refl)

- [x] <:-Trans (Sub_Trans)

- [x] <:-Mono (Sub_Mono)

- [x] Later-<: (Later_Sub)

- [x] <:-Later (Sub_Later)

- [x] T-Skip

- [x] <:-Index-Incr (Sub_Index_Incr)

## Canonical typing lemmas

- [x] T-Nat-I

- [x] T-{}-E (T_Mem_E)

- [x] T-Forall-I

- [x] T-Forall-Ex

- [x] T-Forall-E

- [ ] P-Start

- [ ] P-Sub

- [ ] P-Field

- [ ] P-Later-E

- [ ] Sel-<:

- [ ] <:-Sel

- [x] <:-mu-X (Sub_Mu_X)

## Other semantic typing lemmas

- [x] <:-mu-1 (Sub_Mu_1)

- [x] <:-mu-2 (Sub_Mu_2)

- [x] T-mu-I

- [x] T-mu-E

## Canonical semantic typing lemmas for set-theoretic connectives

- [x] And1-<: (And1_Sub)

- [x] And2-<: (And2_Sub)

- [x] <:-And

- [x] <:-Or1

- [x] <:-Or2

- [x] Or-<:

- [x] <:-Top

- [x] Bot-<:

## Congruence lemmas for subtyping

- [ ] Fld-<:-Fld

- [ ] Typ-<:-Typ

## Creating objects

- [x] T-{}-I (T_New_I) (with big missing lemmas, see `defs_interp_to_interp`)

- [x] D-Typ

- [x] D-Trm

- [ ] D-And
