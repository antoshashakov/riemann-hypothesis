module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentTensorEqZeroOrOneOfIsPurelyInseparable
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open IsLocalRing
open scoped TensorProduct

theorem _root_.GlobalTheory.T.idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable' : ∀ (k K B : Type) [Field k] [Field K] [Algebra k K] [IsPurelyInseparable k K] [CommRing B] [IsLocalRing B] [Algebra k B] (e : K ⊗[k] B), IsIdempotentElem e → e = 0 ∨ e = 1 := by
  first | exact @GlobalTheory.idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable | exact GlobalTheory.idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable | (intros; apply GlobalTheory.idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable <;> assumption)
