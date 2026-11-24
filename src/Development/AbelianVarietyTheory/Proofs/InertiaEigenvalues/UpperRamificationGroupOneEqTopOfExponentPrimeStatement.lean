module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
public import GroundTheory.LocalFields.HerbrandFunction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UpperRamificationGroupOneEqTopOfExponentPrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.upperRamificationGroup_one_eq_top_of_exponent_prime : ∀ (F M : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra F M] [ValuativeExtension F M] [FiniteDimensional F M] [IsGalois F M] (p e : ℕ), p.Prime → 0 < e → OrdIs F p e → upperRamificationGroup F M 0 = ⊤ → (∀ σ : M ≃ₐ[F] M, σ ^ p = 1) → upperRamificationGroup F M 1 = ⊤ := by
  first | exact @GlobalTheory.PMon.Ram.upperRamificationGroup_one_eq_top_of_exponent | exact GlobalTheory.PMon.Ram.upperRamificationGroup_one_eq_top_of_exponent | (intros; apply GlobalTheory.PMon.Ram.upperRamificationGroup_one_eq_top_of_exponent <;> assumption)
