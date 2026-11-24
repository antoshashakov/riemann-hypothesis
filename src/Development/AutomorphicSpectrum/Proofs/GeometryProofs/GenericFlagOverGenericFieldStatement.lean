module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagOverGenericField
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.generic_flag_over_generic_field : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (S : Type) (r : S → ℕ) (V : S → Submodule Ω E) (c : ∀ s, Fin (r s) → E), (∀ s, LinearIndependent Ω (c s) ∧ Submodule.span Ω (Set.range (c s)) = V s) → IsGenericFlag (Ω' := GenField Ω r) (TensorProduct.mk Ω (GenField Ω r) E 1).toAddMonoidHom V (genB c) 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.genB_isGenericFlag | exact GlobalTheory.CompanionTheory.Ar.FlagBun.genB_isGenericFlag | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.genB_isGenericFlag <;> assumption)
