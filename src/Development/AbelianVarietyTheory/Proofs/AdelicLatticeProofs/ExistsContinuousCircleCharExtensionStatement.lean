module

public import Mathlib.Analysis.Complex.Circle
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsContinuousCircleCharExtension
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open scoped Topology

theorem _root_.GlobalTheory.T.exists_continuous_circle_char_extension' : ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] (H N : Subgroup G) (ψ : H →* Circle), IsOpen (H : Set G) → Continuous ψ → (∀ x : H, (x : G) ∈ N → ψ x = 1) → ∃ χ : G →* Circle, Continuous χ ∧ (∀ x ∈ N, χ x = 1) ∧ ∀ x : H, χ x = ψ x := by
  first | exact @GlobalTheory.exists_continuous_circle_char_extension | exact GlobalTheory.exists_continuous_circle_char_extension | (intros; apply GlobalTheory.exists_continuous_circle_char_extension <;> assumption)
