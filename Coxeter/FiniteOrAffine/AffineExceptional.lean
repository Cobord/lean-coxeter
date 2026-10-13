module

public import Coxeter.BilinearLatticeDynkins
public import Coxeter.SpecialFeatures

/-!
# Exceptional affine Coxeter groups

This file reserves names for the exceptional affine Coxeter matrices and Coxeter groups. The matrix
definitions and classification proofs are intentionally left as stubs.
-/

@[expose] public section

namespace Coxeter

axiom affineTypeE6Matrix : CoxeterMatrix (Fin 7)
axiom affineTypeE7Matrix : CoxeterMatrix (Fin 8)
axiom affineTypeE8Matrix : CoxeterMatrix (Fin 9)
axiom affineTypeF4Matrix : CoxeterMatrix (Fin 5)
axiom affineTypeG2Matrix : CoxeterMatrix (Fin 3)

@[reducible] noncomputable def affineTypeE6Group : CoxeterGroup affineTypeE6Matrix.Group where
  B := Fin 7
  M := affineTypeE6Matrix
  cs := affineTypeE6Matrix.toCoxeterSystem

@[reducible] noncomputable def affineTypeE7Group : CoxeterGroup affineTypeE7Matrix.Group where
  B := Fin 8
  M := affineTypeE7Matrix
  cs := affineTypeE7Matrix.toCoxeterSystem

@[reducible] noncomputable def affineTypeE8Group : CoxeterGroup affineTypeE8Matrix.Group where
  B := Fin 9
  M := affineTypeE8Matrix
  cs := affineTypeE8Matrix.toCoxeterSystem

@[reducible] noncomputable def affineTypeF4Group : CoxeterGroup affineTypeF4Matrix.Group where
  B := Fin 5
  M := affineTypeF4Matrix
  cs := affineTypeF4Matrix.toCoxeterSystem

@[reducible] noncomputable def affineTypeG2Group : CoxeterGroup affineTypeG2Matrix.Group where
  B := Fin 3
  M := affineTypeG2Matrix
  cs := affineTypeG2Matrix.toCoxeterSystem

proof_wanted affineTypeE6_isIrreducibleAffineCoxeter :
    @IsIrreducibleAffineCoxeter _ affineTypeE6Group
proof_wanted affineTypeE7_isIrreducibleAffineCoxeter :
    @IsIrreducibleAffineCoxeter _ affineTypeE7Group
proof_wanted affineTypeE8_isIrreducibleAffineCoxeter :
    @IsIrreducibleAffineCoxeter _ affineTypeE8Group
proof_wanted affineTypeF4_isIrreducibleAffineCoxeter :
    @IsIrreducibleAffineCoxeter _ affineTypeF4Group
proof_wanted affineTypeG2_isIrreducibleAffineCoxeter :
    @IsIrreducibleAffineCoxeter _ affineTypeG2Group

proof_wanted affineTypeE6_isIrreducibleAffineWeyl :
    @IsIrreducibleAffineWeyl _ affineTypeE6Group
proof_wanted affineTypeE7_isIrreducibleAffineWeyl :
    @IsIrreducibleAffineWeyl _ affineTypeE7Group
proof_wanted affineTypeE8_isIrreducibleAffineWeyl :
    @IsIrreducibleAffineWeyl _ affineTypeE8Group
proof_wanted affineTypeF4_isIrreducibleAffineWeyl :
    @IsIrreducibleAffineWeyl _ affineTypeF4Group
proof_wanted affineTypeG2_isIrreducibleAffineWeyl :
    @IsIrreducibleAffineWeyl _ affineTypeG2Group


/-! ### Euler lattices of `Ẽ₆`, `Ẽ₇`, `Ẽ₈` -/

/-- The Euler lattice of type `Ẽ₆` (see `Coxeter.BilinearLatticeDynkins`). -/
noncomputable abbrev affineTypeE6BilinearLattice : BilinearLattice.{0} :=
  BilinearLattice.eulerLattice affineTypeE6Matrix

proof_wanted affineTypeE6_isSimplyLaced : BilinearLattice.IsSimplyLaced affineTypeE6Matrix

/-- `S` is quasi-unipotent of index exactly `2`. -/
proof_wanted affineTypeE6BilinearLattice_isQuasiUnipotent :
    Module.End.IsQuasiUnipotentOfIndex
      (affineTypeE6BilinearLattice.S : Module.End ℤ affineTypeE6BilinearLattice) 2 ∧
    ¬ Module.End.IsQuasiUnipotentOfIndex
      (affineTypeE6BilinearLattice.S : Module.End ℤ affineTypeE6BilinearLattice) 1

/-- The Euler lattice of type `Ẽ₇` (see `Coxeter.BilinearLatticeDynkins`). -/
noncomputable abbrev affineTypeE7BilinearLattice : BilinearLattice.{0} :=
  BilinearLattice.eulerLattice affineTypeE7Matrix

proof_wanted affineTypeE7_isSimplyLaced : BilinearLattice.IsSimplyLaced affineTypeE7Matrix

/-- `S` is quasi-unipotent of index exactly `2`. -/
proof_wanted affineTypeE7BilinearLattice_isQuasiUnipotent :
    Module.End.IsQuasiUnipotentOfIndex
      (affineTypeE7BilinearLattice.S : Module.End ℤ affineTypeE7BilinearLattice) 2 ∧
    ¬ Module.End.IsQuasiUnipotentOfIndex
      (affineTypeE7BilinearLattice.S : Module.End ℤ affineTypeE7BilinearLattice) 1

/-- The Euler lattice of type `Ẽ₈` (see `Coxeter.BilinearLatticeDynkins`). -/
noncomputable abbrev affineTypeE8BilinearLattice : BilinearLattice.{0} :=
  BilinearLattice.eulerLattice affineTypeE8Matrix

proof_wanted affineTypeE8_isSimplyLaced : BilinearLattice.IsSimplyLaced affineTypeE8Matrix

/-- `S` is quasi-unipotent of index exactly `2`. -/
proof_wanted affineTypeE8BilinearLattice_isQuasiUnipotent :
    Module.End.IsQuasiUnipotentOfIndex
      (affineTypeE8BilinearLattice.S : Module.End ℤ affineTypeE8BilinearLattice) 2 ∧
    ¬ Module.End.IsQuasiUnipotentOfIndex
      (affineTypeE8BilinearLattice.S : Module.End ℤ affineTypeE8BilinearLattice) 1

end Coxeter
