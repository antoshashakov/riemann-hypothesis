module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteLocalGeomDomain
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open IsLocalRing
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_complete_local_geomDomain' : ∀ (k k' : Type) [Field k] [CommRing k'] [IsDomain k'] [Algebra k k'], Module.Finite k k' → ∃ (C : Type) (_ : CommRing C) (_ : IsLocalRing C) (_ : IsNoetherianRing C) (_ : Algebra k C), IsAdicComplete (maximalIdeal C) C ∧ Nonempty (k' →ₐ[k] ResidueField C) ∧ ∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K → IsPurelyInseparable k K → IsDomain (K ⊗[k] C) := by
  first | exact @GlobalTheory.SepRing.exists_complete_local_geomDomain | exact GlobalTheory.SepRing.exists_complete_local_geomDomain | (intros; apply GlobalTheory.SepRing.exists_complete_local_geomDomain <;> assumption)
