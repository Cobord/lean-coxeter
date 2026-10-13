module

public import Coxeter.BilinearLatticeDynkins
public import Coxeter.SpecialFeatures

/-!
# Affine Coxeter groups of type A

This file reserves names for the affine type `A` Coxeter matrix and Coxeter group. The matrix
definition and classification proof are intentionally left as stubs.
-/

@[expose] public section

namespace Coxeter

axiom affineTypeAMatrix (n : ℕ) : CoxeterMatrix (Fin (n + 1))

@[reducible] noncomputable def affineTypeAGroup (n : ℕ) [NeZero n] :
    CoxeterGroup (affineTypeAMatrix n).Group where
  B := Fin (n + 1)
  M := affineTypeAMatrix n
  cs := (affineTypeAMatrix n).toCoxeterSystem

proof_wanted affineTypeA_isIrreducibleAffineCoxeter (n : ℕ) [NeZero n] :
    @IsIrreducibleAffineCoxeter _ (affineTypeAGroup n)

proof_wanted affineTypeA_isIrreducibleAffineWeyl (n : ℕ) [NeZero n] :
    @IsIrreducibleAffineWeyl _ (affineTypeAGroup n)


/-! ### Euler lattice -/

/-- The Euler lattice of type `Ãₙ` (see `Coxeter.BilinearLatticeDynkins`). It needs `n ≥ 2`:
`Ã₁` is the Kronecker quiver, with a double edge, so it is not simply laced. -/
noncomputable abbrev affineTypeABilinearLattice (n : ℕ) (_ : 2 ≤ n) : BilinearLattice.{0} :=
  BilinearLattice.eulerLattice (affineTypeAMatrix n)

proof_wanted affineTypeA_isSimplyLaced (n : ℕ) (_ : 2 ≤ n) :
    BilinearLattice.IsSimplyLaced (affineTypeAMatrix n)

/-- `S` is quasi-unipotent of index exactly `2`: the null root gives a Jordan block of size `2`
at eigenvalue `1`. -/
proof_wanted affineTypeABilinearLattice_isQuasiUnipotent (n : ℕ) (hn : 2 ≤ n) :
    Module.End.IsQuasiUnipotentOfIndex
      ((affineTypeABilinearLattice n hn).S : Module.End ℤ (affineTypeABilinearLattice n hn)) 2 ∧
    ¬ Module.End.IsQuasiUnipotentOfIndex
      ((affineTypeABilinearLattice n hn).S : Module.End ℤ (affineTypeABilinearLattice n hn)) 1

end Coxeter
