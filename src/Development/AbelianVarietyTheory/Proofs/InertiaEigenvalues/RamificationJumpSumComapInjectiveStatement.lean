module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumComapInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.ramificationJumpSum_comap_injective : ∀ (G G' : Type) [Group G] [Group G'] (j : G' →* G) (R : ℕ → Subgroup G) (B : Subgroup G), Function.Injective j → jumpSum (fun t => (R t).comap j) ⊤ (B.comap j) = jumpSum R j.range B := by
  first | exact @GlobalTheory.PMon.Ram.jumpSum_comap_injective | exact GlobalTheory.PMon.Ram.jumpSum_comap_injective | (intros; apply GlobalTheory.PMon.Ram.jumpSum_comap_injective <;> assumption)
