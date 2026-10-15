module

public import Coxeter.BilinearLatticeDynkins
public import Coxeter.SpecialFeatures

/-!
# Affine Coxeter groups of type D

This file reserves names for the affine type `D` Coxeter matrix and Coxeter group. The matrix
definition and classification proof are intentionally left as stubs.
-/

@[expose] public section

namespace Coxeter

axiom affineTypeDMatrix (n : ℕ) : CoxeterMatrix (Fin (n + 1))

@[reducible] noncomputable def affineTypeDGroup (n : ℕ) [NeZero n] :
    CoxeterGroup (affineTypeDMatrix n).Group where
  B := Fin (n + 1)
  M := affineTypeDMatrix n
  cs := (affineTypeDMatrix n).toCoxeterSystem

proof_wanted affineTypeD_isIrreducibleAffineCoxeter (n : ℕ) [NeZero n] :
    @IsIrreducibleAffineCoxeter _ (affineTypeDGroup n)

proof_wanted affineTypeD_isIrreducibleAffineWeyl (n : ℕ) [NeZero n] :
    @IsIrreducibleAffineWeyl _ (affineTypeDGroup n)


/-! ### Euler lattice -/

section EulerLattice

/-- The Euler lattice of type `D̃ₙ`, `n ≥ 4` (see `Coxeter.BilinearLatticeDynkins`). -/
noncomputable abbrev affineTypeDBilinearLattice (n : ℕ) (_ : 4 ≤ n) : BilinearLattice.{0} :=
  BilinearLattice.eulerLattice (affineTypeDMatrix n)

proof_wanted affineTypeD_isSimplyLaced (n : ℕ) (_ : 4 ≤ n) :
    BilinearLattice.IsSimplyLaced (affineTypeDMatrix n)

/-- `S` is quasi-unipotent of index exactly `2`: the null root gives a Jordan block of size `2`
at eigenvalue `1`. -/
theorem affineTypeDBilinearLattice_isQuasiUnipotent (n : ℕ) (hn : 4 ≤ n) :
    Module.End.IsQuasiUnipotentOfIndex
      ((affineTypeDBilinearLattice n hn).S : Module.End ℤ (affineTypeDBilinearLattice n hn)) 2 ∧
    ¬ Module.End.IsQuasiUnipotentOfIndex
      ((affineTypeDBilinearLattice n hn).S : Module.End ℤ (affineTypeDBilinearLattice n hn)) 1 := by
  sorry

noncomputable abbrev affineTypeDBilinearLatticeWithMonoidQuasiUnipotent (n : ℕ) (hn : 4 ≤ n) :
    BilinearLattice.BilinearLatticeWithMonoidQuasiUnipotent.{0} :=
  BilinearLattice.eulerLatticeWithMonoidQuasiUnipotent
    (M := affineTypeDMatrix n)
    (hS := (affineTypeDBilinearLattice_isQuasiUnipotent n hn).1)

end EulerLattice

end Coxeter
