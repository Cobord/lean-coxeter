# FiniteOrAffine: open `axiom`/`proof_wanted` stubs

Inventory of everything in this directory that is not yet a real proof, as of this writing.
Grouped by file; each item names the declaration and what's needed to close it.

## Finite types

### TypeA.lean
- `proof_wanted typeA_isSimplyLaced (n : ℕ) : BilinearLattice.IsSimplyLaced (CoxeterMatrix.A n)`
- `proof_wanted typeABilinearLattice_S_pow (n : ℕ) : ((typeABilinearLattice n).S : Module.End ℤ _) ^ (n + 1) = 1`
  — Euler-lattice goals (`Coxeter.BilinearLatticeDynkins`). `IsSimplyLaced` is a finite
  entrywise check. The `S_pow` periodicity (Coxeter number `h`) also gives the
  `IsPsdQuasiUnipotent` instance, since `S ^ h = 1` makes `(S ^ h - 1) ^ k = 0` for every `k`;
  with positive semidefiniteness of `bil` this lets `eulerLatticeWithMonoid` build the object.
  For a fixed `n` the power is a matrix computation; for general `n` it needs the explicit
  Coxeter matrix of the linearly oriented path (a companion-type matrix of order `n + 1`).

### TypeD.lean
- `axiom typeD_isFiniteCoxeter (n : ℕ) : @IsFiniteCoxeter _ (typeDGroup (n + 4))` — must stay an
  `axiom` (or become a real proof), not `proof_wanted`, since `typeD_isPolyFiniteWeyl` below
  depends on it as a real term. `D_n`'s Coxeter-Dynkin diagram is a *fork* (a path with one extra
  branch at one end), not a straight path, so it does not directly fit
  `Coxeter.FiniteOrAffine.TridiagonalForm`'s path-with-one-reweighted-edge machinery (used for
  type `B`/`C`). Positive-definiteness needs its own SOS argument (or a fork-shaped generalization
  of `TridiagonalForm`).
- `proof_wanted typeD_isIrreducible (n : ℕ) : @IsIrreducible _ (typeDGroup (n + 4))` — should
  follow the same pattern as `typeA_isIrreducible`/`typeBC_isIrreducible`: show
  `coxeterGraphMatrix (typeDMatrix (n + 4))` is connected (it's a fork, still connected).
- `proof_wanted typeD_isIrreducibleFiniteWeyl (n : ℕ) : @IsIrreducibleFiniteWeyl _ (typeDGroup (n + 4))`
  — trivial once the two items above land: `⟨typeD_isPolyFiniteWeyl n, typeD_isIrreducible n⟩`
  (mirrors `typeBC_isIrreducibleFiniteWeyl`).
- `proof_wanted typeD_isSimplyLaced (n : ℕ) : BilinearLattice.IsSimplyLaced (typeDMatrix (n + 4))`
- `proof_wanted typeDBilinearLattice_S_pow (n : ℕ) : ((typeDBilinearLattice n).S : Module.End ℤ _) ^ (2 * n + 6) = 1`
  — Euler-lattice goals (`Coxeter.BilinearLatticeDynkins`). `IsSimplyLaced` is a finite
  entrywise check. The `S_pow` periodicity (Coxeter number `h`) also gives the
  `IsPsdQuasiUnipotent` instance, since `S ^ h = 1` makes `(S ^ h - 1) ^ k = 0` for every `k`;
  with positive semidefiniteness of `bil` this lets `eulerLatticeWithMonoid` build the object.

### Exceptional.lean
- `proof_wanted typeE6_isIrreducibleFiniteWeyl : @IsIrreducibleFiniteWeyl _ typeE6Group`
- `proof_wanted typeE7_isIrreducibleFiniteWeyl : @IsIrreducibleFiniteWeyl _ typeE7Group`
- `proof_wanted typeE8_isIrreducibleFiniteWeyl : @IsIrreducibleFiniteWeyl _ typeE8Group`
- `proof_wanted typeF4_isIrreducibleFiniteWeyl : @IsIrreducibleFiniteWeyl _ typeF4Group`
- `proof_wanted typeG2_isIrreducibleFiniteWeyl : @IsIrreducibleFiniteWeyl _ typeG2Group`
  — each needs `IsIrreducible` (diagram connectivity, checkable by `fin_cases`/`decide` since
  these are small fixed-rank matrices) plus `IsPolyFiniteWeyl` (`IsFiniteCoxeter ∧
  IsCrystallographic`; crystallographic is already proved for all five). `IsFiniteCoxeter` needs
  positive-definiteness of `bil` — these are fixed, small finite matrices (rank ≤ 8), so in
  principle decidable/computable rather than needing a general SOS argument.
- `proof_wanted typeH3_isIrreducible : @IsIrreducible _ typeH3Group`
- `proof_wanted typeH4_isIrreducible : @IsIrreducible _ typeH4Group` — diagram connectivity,
  should be straightforward (`fin_cases`/`decide` on the fixed rank-3/4 matrix).
- `proof_wanted typeH3_isFiniteCoxeter : @IsFiniteCoxeter _ typeH3Group`
- `proof_wanted typeH4_isFiniteCoxeter : @IsFiniteCoxeter _ typeH4Group` — `H₃`/`H₄` are
  *non-crystallographic* (golden-ratio entries, `cos(π/5)`), so this needs its own
  positive-definiteness argument; not crystallographic, so no `IsPolyFiniteWeyl`/Weyl statement
  applies to these two, only `IsIrreducible ∧ IsFiniteCoxeter` (there's no
  `typeH3_isIrreducibleFiniteWeyl` target, consistent with `H₃`/`H₄` not being Weyl groups).
- `proof_wanted typeE6_isSimplyLaced : BilinearLattice.IsSimplyLaced CoxeterMatrix.E₆`
- `proof_wanted typeE7_isSimplyLaced : BilinearLattice.IsSimplyLaced CoxeterMatrix.E₇`
- `proof_wanted typeE8_isSimplyLaced : BilinearLattice.IsSimplyLaced CoxeterMatrix.E₈`
- `proof_wanted typeE6BilinearLattice_S_pow : (typeE6BilinearLattice.S : Module.End ℤ _) ^ 12 = 1`
- `proof_wanted typeE7BilinearLattice_S_pow : (typeE7BilinearLattice.S : Module.End ℤ _) ^ 18 = 1`
- `proof_wanted typeE8BilinearLattice_S_pow : (typeE8BilinearLattice.S : Module.End ℤ _) ^ 30 = 1`
  — Euler-lattice goals (`Coxeter.BilinearLatticeDynkins`). `IsSimplyLaced` is a finite
  entrywise check. The `S_pow` periodicity (Coxeter number `h`) also gives the
  `IsPsdQuasiUnipotent` instance, since `S ^ h = 1` makes `(S ^ h - 1) ^ k = 0` for every `k`;
  with positive semidefiniteness of `bil` this lets `eulerLatticeWithMonoid` build the object.
  All six are fixed small integer matrices (rank ≤ 8), so `decide`-style computation should work.

## Affine types

Every affine file's *matrix* is still an `axiom` (no actual `CoxeterMatrix` definition yet), which
blocks every downstream `proof_wanted` in that file. Matrix definitions should mirror
`TypeD.lean`'s `typeDMatrix`-style construction (explicit `Matrix.of` with the standard affine
Dynkin diagram shape) or reuse mathlib's affine matrices if/when available.

### AffineTypeA.lean
- `axiom affineTypeAMatrix (n : ℕ) : CoxeterMatrix (Fin (n + 1))`
- `proof_wanted affineTypeA_isIrreducibleAffineCoxeter (n : ℕ) [NeZero n] : @IsIrreducibleAffineCoxeter _ (affineTypeAGroup n)`
- `proof_wanted affineTypeA_isIrreducibleAffineWeyl (n : ℕ) [NeZero n] : @IsIrreducibleAffineWeyl _ (affineTypeAGroup n)`
- `proof_wanted affineTypeA_isSimplyLaced (n : ℕ) (_ : 2 ≤ n) : BilinearLattice.IsSimplyLaced (affineTypeAMatrix n)`
- `proof_wanted affineTypeABilinearLattice_isQuasiUnipotent (n : ℕ) (hn : 2 ≤ n) : IsQuasiUnipotentOfIndex S 2 ∧ ¬ IsQuasiUnipotentOfIndex S 1`
  — Euler-lattice goals (`Coxeter.BilinearLatticeDynkins`), blocked on the matrix axiom like the
  rest of this file. Index exactly `2`: the null root gives a Jordan block of size `2` at
  eigenvalue `1`, so `S` is not of finite order.
  Starts at `n = 2`: `Ã₁` (the Kronecker quiver) has a double edge and is not simply laced.

### AffineTypeB.lean
- `axiom affineTypeBMatrix (n : ℕ) : CoxeterMatrix (Fin (n + 1))`
- `proof_wanted affineTypeB_isIrreducibleAffineCoxeter (n : ℕ) (hn : 2 ≤ n) : @IsIrreducibleAffineCoxeter _ (affineTypeBGroup n hn)`
- `proof_wanted affineTypeB_isIrreducibleAffineWeyl (n : ℕ) (hn : 2 ≤ n) : @IsIrreducibleAffineWeyl _ (affineTypeBGroup n hn)`

### AffineTypeC.lean
- `axiom affineTypeCMatrix (n : ℕ) : CoxeterMatrix (Fin (n + 1))`
- `proof_wanted affineTypeC_isIrreducibleAffineCoxeter (n : ℕ) (hn : 2 ≤ n) : @IsIrreducibleAffineCoxeter _ (affineTypeCGroup n hn)`
- `proof_wanted affineTypeC_isIrreducibleAffineWeyl (n : ℕ) (hn : 2 ≤ n) : @IsIrreducibleAffineWeyl _ (affineTypeCGroup n hn)`
- `proof_wanted affineTypeC_two_identifies_affineTypeB_two : HEq (@CoxeterGroup.cs _ (affineTypeCGroup 2 _)) (@CoxeterGroup.cs _ (affineTypeBGroup 2 _))`
  — the accidental `C₂-hat = B₂-hat` identification; blocked on both `affineTypeCMatrix` and
  `affineTypeBMatrix` actually being defined (currently axioms), same shape as
  `typeBC_one_identifies_typeA_one` once they are.

### AffineTypeD.lean
- `axiom affineTypeDMatrix (n : ℕ) : CoxeterMatrix (Fin (n + 1))`
- `proof_wanted affineTypeD_isIrreducibleAffineCoxeter (n : ℕ) [NeZero n] : @IsIrreducibleAffineCoxeter _ (affineTypeDGroup n)`
- `proof_wanted affineTypeD_isIrreducibleAffineWeyl (n : ℕ) [NeZero n] : @IsIrreducibleAffineWeyl _ (affineTypeDGroup n)`
- `proof_wanted affineTypeD_isSimplyLaced (n : ℕ) (_ : 4 ≤ n) : BilinearLattice.IsSimplyLaced (affineTypeDMatrix n)`
- `proof_wanted affineTypeDBilinearLattice_isQuasiUnipotent (n : ℕ) (hn : 4 ≤ n) : IsQuasiUnipotentOfIndex S 2 ∧ ¬ IsQuasiUnipotentOfIndex S 1`
  — Euler-lattice goals (`Coxeter.BilinearLatticeDynkins`), blocked on the matrix axiom like the
  rest of this file. Index exactly `2`: the null root gives a Jordan block of size `2` at
  eigenvalue `1`, so `S` is not of finite order.
  These use `4 ≤ n` rather than the `[NeZero n]` of the other two goals in this file.

### AffineExceptional.lean
- `axiom affineTypeE6Matrix : CoxeterMatrix (Fin 7)`
- `axiom affineTypeE7Matrix : CoxeterMatrix (Fin 8)`
- `axiom affineTypeE8Matrix : CoxeterMatrix (Fin 9)`
- `axiom affineTypeF4Matrix : CoxeterMatrix (Fin 5)`
- `axiom affineTypeG2Matrix : CoxeterMatrix (Fin 3)`
- `proof_wanted affineTypeE6_isIrreducibleAffineCoxeter : @IsIrreducibleAffineCoxeter _ affineTypeE6Group`
- `proof_wanted affineTypeE7_isIrreducibleAffineCoxeter : @IsIrreducibleAffineCoxeter _ affineTypeE7Group`
- `proof_wanted affineTypeE8_isIrreducibleAffineCoxeter : @IsIrreducibleAffineCoxeter _ affineTypeE8Group`
- `proof_wanted affineTypeF4_isIrreducibleAffineCoxeter : @IsIrreducibleAffineCoxeter _ affineTypeF4Group`
- `proof_wanted affineTypeG2_isIrreducibleAffineCoxeter : @IsIrreducibleAffineCoxeter _ affineTypeG2Group`
- `proof_wanted affineTypeE6_isIrreducibleAffineWeyl : @IsIrreducibleAffineWeyl _ affineTypeE6Group`
- `proof_wanted affineTypeE7_isIrreducibleAffineWeyl : @IsIrreducibleAffineWeyl _ affineTypeE7Group`
- `proof_wanted affineTypeE8_isIrreducibleAffineWeyl : @IsIrreducibleAffineWeyl _ affineTypeE8Group`
- `proof_wanted affineTypeF4_isIrreducibleAffineWeyl : @IsIrreducibleAffineWeyl _ affineTypeF4Group`
- `proof_wanted affineTypeG2_isIrreducibleAffineWeyl : @IsIrreducibleAffineWeyl _ affineTypeG2Group`
- `proof_wanted affineTypeE6_isSimplyLaced : BilinearLattice.IsSimplyLaced affineTypeE6Matrix`
- `proof_wanted affineTypeE7_isSimplyLaced : BilinearLattice.IsSimplyLaced affineTypeE7Matrix`
- `proof_wanted affineTypeE8_isSimplyLaced : BilinearLattice.IsSimplyLaced affineTypeE8Matrix`
- `proof_wanted affineTypeE6BilinearLattice_isQuasiUnipotent : IsQuasiUnipotentOfIndex S 2 ∧ ¬ IsQuasiUnipotentOfIndex S 1`
- `proof_wanted affineTypeE7BilinearLattice_isQuasiUnipotent : IsQuasiUnipotentOfIndex S 2 ∧ ¬ IsQuasiUnipotentOfIndex S 1`
- `proof_wanted affineTypeE8BilinearLattice_isQuasiUnipotent : IsQuasiUnipotentOfIndex S 2 ∧ ¬ IsQuasiUnipotentOfIndex S 1`
  — Euler-lattice goals (`Coxeter.BilinearLatticeDynkins`), blocked on the matrix axiom like the
  rest of this file. Index exactly `2`: the null root gives a Jordan block of size `2` at
  eigenvalue `1`, so `S` is not of finite order.
  `F̃₄`/`G̃₂` are not simply laced, so they have no Euler lattice here (they need valued quivers).

## Suggested order of attack

1. `TypeD.lean`'s `typeD_isIrreducible` and `typeD_isIrreducibleFiniteWeyl` — cheap, unblocks the
   file entirely except for `typeD_isFiniteCoxeter`'s SOS argument.
2. `Exceptional.lean`'s `IsIrreducible` goals for `H₃`/`H₄` — connectivity only, cheap.
3. `TypeD.lean`'s `typeD_isFiniteCoxeter` (downgrade `axiom` → real proof) — needs a fork-shaped
   SOS identity; could motivate a second generalization in `TridiagonalForm.lean` (or a sibling
   file) analogous to the `lastEdge`-reweighting one already there for type `B`/`C`.
4. `Exceptional.lean`'s five `IsIrreducibleFiniteWeyl` goals and two `H₃`/`H₄` `IsFiniteCoxeter`
   goals — fixed small rank, so brute-force/`decide`-style positive-definiteness may be more
   tractable than a general argument; the rank-2 machinery in `Coxeter.GeometricRepresentation`
   (`bil_restrict_E_diag`/`bil_restrict_E_isPosSemidef`/`bil_restrict_E_nondegenerate_iff`, now
   public) generalizes to any pair of generators, not just rank-2 whole diagrams, and may help.
5. Affine files last: every affine matrix is currently just an `axiom`, so nothing there can be
   proved until the actual matrices are defined.
