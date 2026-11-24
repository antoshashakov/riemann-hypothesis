module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndepOnPowOfIsDomainTensorPurelyInseparabl
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.linearIndepOn_frob_pow_of_isDomain_tensor_insep : ∀ (k B : Type) [Field k] [CommRing B] [IsDomain B] [Algebra k B] (p : ℕ), p.Prime → CharP k p → (∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K → IsPurelyInseparable k K → IsDomain (K ⊗[k] B)) → ∀ s : Finset (FractionRing B), LinearIndepOn k _root_.id (s : Set (FractionRing B)) → LinearIndepOn k (· ^ p) (s : Set (FractionRing B)) := by
  first | exact @GlobalTheory.linearIndepOn_pow_of_isDomain_tensor_purelyInseparable | exact GlobalTheory.linearIndepOn_pow_of_isDomain_tensor_purelyInseparable | (intros; apply GlobalTheory.linearIndepOn_pow_of_isDomain_tensor_purelyInseparable <;> assumption)
