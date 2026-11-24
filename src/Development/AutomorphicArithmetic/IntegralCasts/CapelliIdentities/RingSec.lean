module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Supplements.MathlibImports.AnalysisAndTactics
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.RingTheory.Jacobson.Ring

@[expose] public section

theorem UpperTheory.Reformulated.B.Qh66.ring_sec :
    ∀ (Ω C : Type) [inst : Field Ω] [IsAlgClosed Ω]
    [inst_2 : CommRing C] [Nontrivial C] (φ : Ω →+* C), φ.FiniteType → ∃ (ρ : C →+* Ω), ρ.comp φ = RingHom.id Ω := by
  intro Ω C _ _ _ _ φ hφ
  letI : Algebra Ω C := φ.toAlgebra
  haveI : Algebra.FiniteType Ω C := hφ
  obtain ⟨m, hm⟩ := Ideal.exists_maximal C
  letI : Field (C ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite Ω (C ⧸ m) := finite_of_finite_type_of_isJacobsonRing Ω (C ⧸ m)
  let f : (C ⧸ m) →ₐ[Ω] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨(f.comp (Ideal.Quotient.mkₐ Ω m)).toRingHom, ?_⟩
  ext x
  exact (f.comp (Ideal.Quotient.mkₐ Ω m)).commutes x
