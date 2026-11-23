module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHermitianLogUnitaryBlockDiagonal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.EqZeroOfPiInf

@[expose] public section

noncomputable section

open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.RealLift.KLineProof

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piInf_tmul {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) (e : E) :
    piInf τ (a ⊗ₜ[F] e) = InfinitePlace.Completion.extensionEmbedding w (evInf F w a) * τ.1 e := by
  simp [piInf, compInf, infEmb]

theorem ext_star {w : InfinitePlace F} (hw : w.IsReal) (x : w.Completion) :
    star (InfinitePlace.Completion.extensionEmbedding w x) = InfinitePlace.Completion.extensionEmbedding w x := by
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw x]
  exact Complex.conj_ofReal _

theorem piInf_cA {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (x : AE F E) :
    piInf τ (cA σ x) = star (piInf τ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    have h1 : cA σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := by simp [cA]
    rw [h1, piInf_tmul, piInf_tmul, star_mul', ext_star (hCM.1.isReal w), hCM.2.2.2]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), star_add]

theorem exists_moved {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    ∃ e : E, σ e ≠ e := by
  by_contra h
  push Not at h
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hr : ComplexEmbedding.IsReal (τ w).1 := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have := hCM.2.2.2 (τ w).1 x
    rw [h x] at this
    rw [ComplexEmbedding.conjugate_coe_eq, starRingEnd_apply]
    exact this.symm
  haveI := hCM.2.1
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk (τ w).1)))
    (InfinitePlace.isReal_mk_iff.2 hr)

theorem eq_zero_of_piInf {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (d : AE F E)
    (hd : At (evI F) d) (h0 : ∀ w, piInf (τ w) d = 0) : d = 0 :=
  GlobalTheory.CompanionTheory.CMAdele.eq_zero_of_piInf σ hCM τ d hd h0

theorem Jm_mul_Jm (R S : ℕ) : Jm R S * Jm R S = 1 := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem Jm_map_star (R S : ℕ) : (Jm R S).map star = Jm R S := by
  ext a b; rcases a with i | i <;> rcases b with j | j <;>
    simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks, Matrix.one_apply] <;> split_ifs <;> simp

theorem Jm_conjTranspose (R S : ℕ) : (Jm R S)ᴴ = Jm R S := by
  ext a b; rcases a with i | i <;> rcases b with j | j <;>
    simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks, Matrix.one_apply, Matrix.conjTranspose_apply] <;> split_ifs <;> simp_all [eq_comm]

theorem star_mul_one {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] (X : Matrix m n ℂ) (Y : Matrix n m ℂ)
    (h : X * Y.map star = 1) : X.map star * Y = 1 := by
  have := congrArg (fun Z => Z.map (starRingEnd ℂ)) h
  simp only [Matrix.map_mul] at this
  ext i j
  have h2 := congrFun (congrFun this i) j
  simp only [Matrix.map_apply, Matrix.map_map] at h2
  convert h2 using 1
  · simp [Matrix.mul_apply]
  · simp [Matrix.one_apply]

theorem frame_inv {β : Type} [Fintype β] [DecidableEq β] {R S : ℕ} {M : Matrix β β ℂ} {C : Matrix β (Ix R S) ℂ}
    (h : GlobalTheory.RealLift.IsFrame M C) : ∃ A' : Matrix (Ix R S) β ℂ, C * A' = 1 ∧ A' * C = 1 := by
  obtain ⟨h1, A', hA⟩ := h
  refine ⟨A', hA, ?_⟩
  have e1 : (Jm R S * Cᵀ * M) * C.map star = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Cᵀ, h1, Jm_mul_Jm]
  have e2 : (Jm R S * Cᵀ * M).map star * C = 1 := star_mul_one _ _ e1
  calc A' * C = ((Jm R S * Cᵀ * M).map star * C) * A' * C := by rw [e2, Matrix.one_mul]
    _ = (Jm R S * Cᵀ * M).map star * (C * A') * C := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hA, Matrix.mul_one, e2]

theorem map_star_mul {m n o : Type} [Fintype n] (X : Matrix m n ℂ) (Y : Matrix n o ℂ) :
    (X * Y).map star = X.map star * Y.map star :=
  Matrix.map_mul (f := starRingEnd ℂ)

theorem exists_gen_at {β : Type} [Fintype β] [DecidableEq β] {R S : ℕ} (C : Matrix β (Ix R S) ℂ)
    (A' : Matrix (Ix R S) β ℂ) (hCA : C * A' = 1) (hAC : A' * C = 1) (Jw : Matrix β β ℂ) (b : ℂ)
    (h1 : Cᵀ * (b • Jw) * C.map star = Jm R S) (kw θ : Matrix β β ℂ) (hk : kwᵀ * Jw * kw.map star = Jw)
    (hθ : θ * C = C * Jm R S) (hkθ : Commute kw θ) :
    ∃ Y : Mat R S, Y ∈ upq R S ∧ IsKC Y ∧ C * NormedSpace.exp Y = kw * C := by
  set g : Mat R S := A' * kw * C with hg
  have t1 : A'ᵀ * Cᵀ = 1 := by rw [← Matrix.transpose_mul, hCA, Matrix.transpose_one]
  have t2 : C.map star * A'.map star = 1 := by
    rw [← map_star_mul, hCA]; exact Matrix.map_one _ (star_zero _) (star_one _)
  have hJ : gᵀ * Jm R S * g.map star = Jm R S := by
    calc gᵀ * Jm R S * g.map star
        = Cᵀ * (kwᵀ * ((A'ᵀ * Cᵀ) * (b • Jw) * (C.map star * A'.map star)) * kw.map star) * C.map star := by
          rw [← h1]; simp only [hg, Matrix.transpose_mul, map_star_mul, Matrix.mul_assoc]
      _ = Cᵀ * (b • Jw) * C.map star := by
          rw [t1, t2, Matrix.one_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, hk]
      _ = Jm R S := h1
  have hJ' : Jm R S = A' * θ * C := by rw [Matrix.mul_assoc, hθ, ← Matrix.mul_assoc, hAC, Matrix.one_mul]
  have hcomm : Commute g (Jm R S) := by
    have e1 : g * Jm R S = A' * (kw * θ) * C := by
      calc g * Jm R S = A' * kw * (C * A') * θ * C := by rw [hJ']; simp only [hg, Matrix.mul_assoc]
        _ = _ := by rw [hCA, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    have e2 : Jm R S * g = A' * (θ * kw) * C := by
      calc Jm R S * g = A' * θ * (C * A') * kw * C := by rw [hJ']; simp only [hg, Matrix.mul_assoc]
        _ = _ := by rw [hCA, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    show g * Jm R S = Jm R S * g
    rw [e1, e2, hkθ.eq]
  have hJ2 : gᴴ * Jm R S * g = Jm R S := by
    have := congrArg (fun Z => Z.map star) hJ
    simp only [map_star_mul, Jm_map_star] at this
    have e : (g.map star).map star = g := by ext i j; simp
    rw [e] at this
    exact this
  have hunit : star g * g = 1 := by
    rw [Matrix.star_eq_conjTranspose]
    calc gᴴ * g = gᴴ * g * (Jm R S * Jm R S) := by rw [Jm_mul_Jm, Matrix.mul_one]
      _ = gᴴ * (g * Jm R S) * Jm R S := by simp only [Matrix.mul_assoc]
      _ = gᴴ * Jm R S * g * Jm R S := by rw [hcomm.eq]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJ2, Jm_mul_Jm]
  have hu : g ∈ unitary (Mat R S) := Matrix.mem_unitaryGroup_iff'.2 hunit
  obtain ⟨H, hH, -, hexp, hcomH⟩ := GlobalTheory.CartanInt.UnitLog.exists_log g hu
  have hstar : Commute (star g) (Jm R S) := by
    have := hcomm.star_star
    rwa [Matrix.star_eq_conjTranspose (Jm R S), Jm_conjTranspose] at this
  have hKC : Commute H (Jm R S) := hcomH _ hcomm hstar
  refine ⟨Complex.I • H, ?_, ?_, ?_⟩
  · show (Complex.I • H)ᴴ * Jm R S + Jm R S * (Complex.I • H) = 0
    rw [Matrix.conjTranspose_smul, hH, Matrix.smul_mul, Matrix.mul_smul, hKC.eq]
    simp [Complex.conj_I]
  · exact (GlobalTheory.CartanInt.UnitLog.isKC_iff_commute _).2 (hKC.smul_left Complex.I)
  · rw [← hexp, hg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hCA, Matrix.one_mul]

theorem map_cA_map {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {β : Type} {w : InfinitePlace F} (τ : EmbOver E w)
    (K : Matrix β β (AE F E)) : (K.map (cA σ)).map (piInf τ) = (K.map (piInf τ)).map star := by
  ext i j; simp [piInf_cA hCM]

end GlobalTheory.RealLift.KLineProof

namespace GlobalTheory.RealLift

open GlobalTheory.RealLift.KLineProof

theorem kLine_of_lineEx (hL : LineEx) : KLine := by
  intro F E _ _ _ _ _ σ β _ _ R S τ J b C θ hCM hfr hθ k hk hkθ
  have hu : (k.1 : Matrix β β (AE F E))ᵀ * J * (k.1 : Matrix β β (AE F E)).map (cA σ) = J := k.2
  have hloc : ∀ w, ∃ Y : Mat R S, Y ∈ upq R S ∧ IsKC Y ∧
      C w * NormedSpace.exp Y = (k.1 : Matrix β β (AE F E)).map (piInf (τ w)) * C w := by
    intro w
    obtain ⟨A', hCA, hAC⟩ := frame_inv (hfr w)
    refine exists_gen_at (C w) A' hCA hAC (J.map (piInf (τ w))) b (hfr w).1 _ (θ w) ?_ (hθ w) (hkθ w)
    have := congrArg (fun X => X.map (piInf (τ w))) hu
    simp only [Matrix.map_mul, map_cA_map hCM, Matrix.transpose_map] at this
    exact this
  choose Y hY using hloc
  obtain ⟨γ, hγ, hgen⟩ := hL F E σ β R S τ J b C hCM hfr Y (fun w => (hY w).1)
  refine ⟨γ, hγ, Y, hgen, fun w => (hY w).2.1, ?_⟩
  have hw : ∀ w, ((γ (Multiplicative.ofAdd 1)).1 : Matrix β β (AE F E)).map (piInf (τ w)) =
      (k.1 : Matrix β β (AE F E)).map (piInf (τ w)) := by
    intro w
    obtain ⟨A', hCA, -⟩ := frame_inv (hfr w)
    have h1 := hgen 1 w
    rw [one_smul, (hY w).2.2] at h1
    calc _ = ((γ (Multiplicative.ofAdd 1)).1 : Matrix β β (AE F E)).map (piInf (τ w)) * C w * A' := by
          rw [Matrix.mul_assoc, hCA, Matrix.mul_one]
      _ = _ := by rw [h1, Matrix.mul_assoc, hCA, Matrix.mul_one]
  have hA1 := hγ.2 (Multiplicative.ofAdd 1)
  have hmat : ((γ (Multiplicative.ofAdd 1)).1 : Matrix β β (AE F E)) = k.1 := by
    ext i j
    rw [← sub_eq_zero]
    refine eq_zero_of_piInf hCM τ _ ?_ ?_
    · intro u hu0
      have e1 := congrFun (congrFun (hA1 u hu0) i) j
      have e2 := congrFun (congrFun (hk u hu0) i) j
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply, smul_sub] at e1 e2 ⊢
      rw [← sub_sub_sub_cancel_right _ _ (u • (1 : Matrix β β (AE F E)) i j), e1, e2, sub_zero]
    · intro w
      have := congrFun (congrFun (hw w) i) j
      simp only [Matrix.map_apply] at this
      rw [map_sub, this, sub_self]
  exact Subtype.ext (Units.ext hmat)

end GlobalTheory.RealLift
