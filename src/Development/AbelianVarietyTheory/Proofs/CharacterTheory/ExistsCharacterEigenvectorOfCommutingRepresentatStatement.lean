module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RepresentationTheory.Basic
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCharacterEigenvectorOfCommutingRepresentat
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.exists_character_eigenvector_of_commuting_representation : ∀ (L : Type) [Field L] [IsAlgClosed L] (B : Type) [Group B] (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] [Nontrivial V] (ρ : Representation L B V), (∀ a b, ρ a * ρ b = ρ b * ρ a) → ∃ (lam : B →* Lˣ) (v : V), v ≠ 0 ∧ ∀ b, ρ b v = (lam b : L) • v := by
  first | exact @GlobalTheory.exists_character_eigenvector_of_commute | exact GlobalTheory.exists_character_eigenvector_of_commute | (intros; apply GlobalTheory.exists_character_eigenvector_of_commute <;> assumption)
