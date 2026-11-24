module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumEqSumRange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.ramificationJumpSum_eq_sum_range : ∀ (G : Type) [Group G] (R : ℕ → Subgroup G) (A B : Subgroup G) (n : ℕ), Antitone R → (∀ t, t < n ↔ ¬ A ⊓ R t ≤ B) → jumpSum R A B = ∑ t ∈ Finset.range n, Nat.card ↥(A ⊓ R t) := by
  first | exact @GlobalTheory.PMon.Ram.jumpSum_eq_sum_range | exact GlobalTheory.PMon.Ram.jumpSum_eq_sum_range | (intros; apply GlobalTheory.PMon.Ram.jumpSum_eq_sum_range <;> assumption)
