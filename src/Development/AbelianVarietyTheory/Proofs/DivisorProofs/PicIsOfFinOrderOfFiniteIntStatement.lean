module

public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicIsOfFinOrderOfFiniteInt
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.pic_isOfFinOrder_of_finite_int' : ∀ (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B] (M : CommRing.Pic B), IsOfFinOrder M := by
  first | exact @GlobalTheory.pic_isOfFinOrder_of_finite_int | exact GlobalTheory.pic_isOfFinOrder_of_finite_int | (intros; apply GlobalTheory.pic_isOfFinOrder_of_finite_int <;> assumption)
