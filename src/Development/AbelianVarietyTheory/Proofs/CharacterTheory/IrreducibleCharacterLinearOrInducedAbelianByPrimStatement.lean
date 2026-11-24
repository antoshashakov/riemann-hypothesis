module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IrreducibleCharacterLinearOrInducedAbelianByPrim
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open GlobalTheory.BI

theorem _root_.GlobalTheory.T.irreducibleCharacter_linear_or_induced_abelianByPrimePower : ∀ (L : Type) [Field L] [CharZero L] [IsAlgClosed L] (G : Type) [Group G] [Finite G] (χ : G → L), AbByP G → IsIrrChar L L χ → (∃ lam : G →* Lˣ, ∀ g, χ g = (lam g : L)) ∨ ∃ T : Subgroup G, T ≠ ⊤ ∧ ∃ ψ : T → L, IsChar L L ψ ∧ χ = ind T ψ := by
  first | exact @GlobalTheory.BI.irrChar_linear_or_induced | exact GlobalTheory.BI.irrChar_linear_or_induced | (intros; apply GlobalTheory.BI.irrChar_linear_or_induced <;> assumption)
