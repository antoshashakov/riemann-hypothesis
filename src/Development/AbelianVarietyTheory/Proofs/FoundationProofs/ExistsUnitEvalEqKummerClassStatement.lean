module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Letter
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitEvalEqKummerClass
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

theorem _root_.GlobalTheory.T.exists_unit_eval_eq_kummer_class : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l n : ℕ) [Fact l.Prime], ∀ a ∈ X.A l, ∃ f ∈ X.Un (l ^ n), AdicCompletion.eval (idl l) (X.Kl l) n a = X.cls l n f := by
  first | exact @GlobalTheory.KZ.ES.exists_un_eval_eq_cls | exact GlobalTheory.KZ.ES.exists_un_eval_eq_cls | (intros; apply GlobalTheory.KZ.ES.exists_un_eval_eq_cls <;> assumption)
