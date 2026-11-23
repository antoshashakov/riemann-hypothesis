module

public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.Complementary
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.TwKerLeComapOf
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.WhittakerModels.WhitCuspOfSegCuspGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductionFiniteLength
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspProdCharTransport
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductHasFiniteLengthGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestDerivativeOfProduct
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothIterPhi
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIrreducibleTensorDecomposition
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
import GroundTheory.LocalFields.PadicLogSeries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.DerFin

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.BZMir
open scoped TensorProduct

namespace CompanionTheory.RgGu.NR.DerFin

section Gen

variable {G M V W X : Type} [Group G] [Group M] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X] (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
  (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n)

def dMap {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (f : ρ.IntertwiningMap σ) :
    (twAct ρ N θ s hs).IntertwiningMap (twAct σ N θ s hs) :=
  ⟨twMap ρ σ N θ f.toLinearMap (fun g v => Representation.IntertwiningMap.isIntertwining _ _ f g v), fun m =>
    Submodule.linearMap_qext _ (LinearMap.ext fun v => by
      show Submodule.Quotient.mk (f (ρ (s m) v)) = Submodule.Quotient.mk (σ (s m) (f v))
      rw [Representation.IntertwiningMap.isIntertwining])⟩

theorem dMap_mk {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (f : ρ.IntertwiningMap σ) (v : V) :
    dMap N θ s hs f (Submodule.Quotient.mk v) = Submodule.Quotient.mk (f v) := rfl

theorem dMap_surjective {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (f : ρ.IntertwiningMap σ)
    (hf : Function.Surjective f) : Function.Surjective (dMap N θ s hs f) := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H w =>
    obtain ⟨v, rfl⟩ := hf w
    exact ⟨Submodule.Quotient.mk v, rfl⟩

theorem twKer_le_map {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (p : ρ.IntertwiningMap σ)
    (hp : Function.Surjective p) : twKer σ N θ ≤ (twKer ρ N θ).map p.toLinearMap := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨n, y, rfl⟩
  obtain ⟨v, rfl⟩ := hp y
  refine ⟨ρ (n : G) v - (θ n : ℂ) • v, Submodule.subset_span ⟨n, v, rfl⟩, ?_⟩
  show p (ρ (n : G) v - (θ n : ℂ) • v) = σ (n : G) (p v) - (θ n : ℂ) • p v
  rw [map_sub, map_smul, Representation.IntertwiningMap.isIntertwining]

theorem d_exact {ρ₁ : Representation ℂ G V} {ρ₂ : Representation ℂ G W} {ρ₃ : Representation ℂ G X}
    (ι : ρ₁.IntertwiningMap ρ₂) (p : ρ₂.IntertwiningMap ρ₃) (hp : Function.Surjective p)
    (hex : ∀ v, p v = 0 → ∃ u, ι u = v) :
    ∀ x, dMap N θ s hs p x = 0 → ∃ y, dMap N θ s hs ι y = x := by
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    rw [dMap_mk, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨w, hw, hpw⟩ := twKer_le_map N θ p hp hx
    obtain ⟨u, hu⟩ := hex (v - w) (by rw [map_sub]; exact sub_eq_zero.2 hpw.symm)
    refine ⟨Submodule.Quotient.mk u, ?_⟩
    rw [dMap_mk, hu, Submodule.Quotient.mk_sub, (Submodule.Quotient.mk_eq_zero _).2 hw, sub_zero]

omit [Group M] in
theorem subsingleton_tw {ρ : Representation ℂ G V} [Subsingleton V] : Subsingleton (TwJacquet ρ N θ) :=
  ⟨fun x y => by
    induction x using Submodule.Quotient.induction_on with
    | H a =>
      induction y using Submodule.Quotient.induction_on with
      | H b => rw [Subsingleton.elim a b]⟩

def topBot (ρ : Representation ℂ G V) : (subQuot (⊤ : Subrepresentation ρ) ⊥).IntertwiningMap ρ :=
  ⟨Submodule.liftQ _ (⊤ : Subrepresentation ρ).toSubmodule.subtype (fun x hx => by
      rw [LinearMap.mem_ker]
      exact (Submodule.mem_bot ℂ).1 hx), fun g => Submodule.linearMap_qext _ (LinearMap.ext fun x => rfl)⟩

theorem topBot_surjective (ρ : Representation ℂ G V) : Function.Surjective (topBot ρ) :=
  fun v => ⟨Submodule.Quotient.mk ⟨v, trivial⟩, rfl⟩

end Gen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Base

variable (ψ : AddChar k Circle) {n t : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def phi (n t : ℕ) : Levi k (fun a : Fin 2 => Fin (![n, t] a)) →* GL (Fin n) k × GL (Fin t) k :=
  (Pi.evalMonoidHom (fun a : Fin 2 => GL (Fin (![n, t] a)) k) 0).prod
    (Pi.evalMonoidHom (fun a : Fin 2 => GL (Fin (![n, t] a)) k) 1)

def lift2 {n t : ℕ} (g : GL (Fin n) k) (h : GL (Fin t) k) : Levi k (fun a : Fin 2 => Fin (![n, t] a)) :=
  fun a => match a with
    | ⟨0, _⟩ => g
    | ⟨1, _⟩ => h
    | ⟨i + 2, hi⟩ => absurd hi (by omega)

theorem phi_lift2 {n t : ℕ} (g : GL (Fin n) k) (h : GL (Fin t) k) : phi n t (lift2 g h) = (g, h) := rfl

theorem phi_surjective (n t : ℕ) : Function.Surjective (phi (k := k) n t) := by
  rintro ⟨g, h⟩
  exact ⟨lift2 g h, phi_lift2 g h⟩

theorem phi_continuous (n t : ℕ) : Continuous (phi (k := k) n t) :=
  (continuous_apply 0).prodMk (continuous_apply 1)

theorem finLen (hc : Continuous ψ) (h1 : ψ ≠ 1) (Mr : Representation ℂ (GL (Fin n) k × GL (Fin t) k) V)
    (hMs : IsSmooth Mr) (hM : HasFiniteLength Mr) :
    HasFiniteLength (twAct Mr (rightUnip k n t) (rightWhit k ψ n t) (MonoidHom.inl _ _) (inl_stab ψ n t)) := by
  obtain ⟨hgt, hlt⟩ := (hasFiniteLength_iff_wellFounded Mr).1 hM
  have key : ∀ S T : Subrepresentation Mr, T ≤ S →
      HasFiniteLength (twAct (subQuot S T) (rightUnip k n t) (rightWhit k ψ n t) (MonoidHom.inl _ _)
        (inl_stab ψ n t)) := by
    intro S₀
    refine WellFoundedLT.induction (motive := fun S => ∀ T, T ≤ S →
      HasFiniteLength (twAct (subQuot S T) (rightUnip k n t) (rightWhit k ψ n t) (MonoidHom.inl _ _)
        (inl_stab ψ n t))) S₀ ?_
    intro S ihS T₀
    refine WellFoundedGT.induction (motive := fun T => T ≤ S →
      HasFiniteLength (twAct (subQuot S T) (rightUnip k n t) (rightWhit k ψ n t) (MonoidHom.inl _ _)
        (inl_stab ψ n t))) T₀ ?_
    intro T ihT hTS
    rcases eq_or_lt_of_le hTS with hEq | hlt'
    · subst hEq
      haveI := GlobalTheory.ParIndExact.subsingleton_subQuot_self T
      haveI := subsingleton_tw (ρ := subQuot T T) (rightUnip k n t) (rightWhit k ψ n t)
      exact GlobalTheory.ProdLength.hasFiniteLength_of_subsingleton _
    by_cases hcov : T ⋖ S
    · exact _root_.PositivityTheory.RgGu.NR.DerFin.base ψ hc h1 _ ((GlobalTheory.ParIndExact.isSubquotient_subQuot S T).isSmooth hMs)
        (GlobalTheory.SmGL.isIrreducible_subQuot hcov)
    obtain ⟨U, hTU, hUS⟩ : ∃ U, T < U ∧ U < S := by
      by_contra hno
      exact hcov ⟨hlt', fun U h1' h2' => hno ⟨U, h1', h2'⟩⟩
    obtain ⟨ι, p, -, hp, -, hex⟩ := GlobalTheory.ParIndExact.subQuot_exact (ρ := Mr) hTU.le hUS.le
    exact GlobalTheory.ProdLength.hasFiniteLength_of_exact (dMap _ _ _ _ ι) (dMap _ _ _ _ p)
      (d_exact _ _ _ _ ι p hp hex) (ihS U hUS T hTU.le) (ihT U hTU hUS.le)
  exact GlobalTheory.JacquetBlocks.hasFiniteLength_of_surjective (dMap _ _ _ _ (topBot Mr))
    (dMap_surjective _ _ _ _ _ (topBot_surjective Mr)) (key ⊤ ⊥ bot_le)

end Base

end CompanionTheory.RgGu.NR.DerFin

namespace CompanionTheory.RgGu.NR

open CompanionTheory.RgGu.NR.DerFin

theorem derFin_of (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (h : DerEquiv k) : DerFin k := by
  intro ψ hc h1 n j V _ _ π hs hi
  obtain ⟨E⟩ := h ψ n j V π
  have hfl : HasFiniteLength π := GlobalTheory.SmGL.hasFiniteLength_of_isIrreducible hi
  have hJ : HasFiniteLength (jac (two (stdSum (show n + (j + 1) = n + j + 1 from rfl))) π) :=
    (GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k).2.1 _ _ _ _ V π hs hfl
  have hJU : HasFiniteLength (jacU₂ (stdSum (show n + (j + 1) = n + j + 1 from rfl)) π) :=
    (hasFiniteLength_comp_iff _ _ (leviTwo k (Fin n) (Fin (j + 1))).surjective).2
      ((GlobalTheory.JacquetBlocks.hasFiniteLength_twist_iff _ _).1 hJ)
  have hJs : IsSmooth (jacU₂ (stdSum (show n + (j + 1) = n + j + 1 from rfl)) π) :=
    isSmooth_comp (isSmooth_jacU _ hs) _ (continuous_leviTwo k)
  exact HasFiniteLength.of_equiv (finLen ψ hc h1 _ hJs hJU) E.symm

end CompanionTheory.RgGu.NR
