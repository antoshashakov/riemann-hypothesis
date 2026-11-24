module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
public import GroundTheory.LocalFields.HerbrandFunction
public import GroundTheory.LocalFields.SeparableClosure
public import Mathlib.FieldTheory.Galois.Abelian
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMemUpperRamificationGroupAbelianNat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.pow_mem_upperRamificationGroup_abelian_nat' : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (M : IntermediateField F (SeparableClosure F)) [FiniteDimensional F ↥M] [IsAbelianGalois F ↥M] (p e n : ℕ), OrdIs F p e → ∀ σ ∈ upperRamificationGroup F ↥M (n : ℝ), σ ^ p ∈ upperRamificationGroup F ↥M ((min (2 * n) (n + e) : ℕ) : ℝ) := by
  first | exact @GlobalTheory.PMon.Ram.pow_mem_upperRamificationGroup_abelian_nat | exact GlobalTheory.PMon.Ram.pow_mem_upperRamificationGroup_abelian_nat | (intros; apply GlobalTheory.PMon.Ram.pow_mem_upperRamificationGroup_abelian_nat <;> assumption)
