import Lib.General.Analysis.HolomorphicIntegrals
import Lib.Shimura.Uniformisation.HolomorphicFamilies

/-! General lemmas of algebraic geometry (textbook or folklore).

This file: Smoothness from a tangent bound and an immersed generic holomorphic family. -/

alias ⟨_, Function.Injective.of_ker⟩ := injective_iff_map_eq_zero

namespace New

open CategoryTheory AlgebraicGeometry Spec Set IsLocalRing CommRingCat TrivSqZeroExt Algebra Module
  TensorProduct MvPolynomial KaehlerDifferential IsLocalization.Away Localization LinearMap RingHom
  Cardinal New.PointFn HasRingHomProperty IsStandardSmoothOfRelativeDimension

open CategoryTheory AlgebraicGeometry Spec Set IsLocalRing CommRingCat TrivSqZeroExt Algebra Module
  TensorProduct MvPolynomial KaehlerDifferential IsLocalization.Away Localization LinearMap RingHom
  Cardinal PointFn HasRingHomProperty IsStandardSmoothOfRelativeDimension
attribute [local simp] map_inj ConcreteCategory.hom_ext_iff

/-- Let X be locally of finite type over a normal domain R ⊂ ℂ, φ a d-parameter family of
complex points over R, immersive at b, with φ(b) specialising to nearby members, and a: Spec
V → X extend φ(b). If the relative tangent space at the closed point of a has dimension ≤ d,
X is smooth of relative dimension d on an open set containing a. -/
lemma Variety.exists_landsIn_smoothOfRelativeDimension {d : ℕ} {X : Scheme} {R : CommRingCat}
    {w₀ : Fin d → ℂ}
    {emb : R ⟶ of ℂ} {k : Type} {φ : (Fin d → ℂ) → (Spec (of ℂ) ⟶ X)} {V : ValuationSubring ℂ}
    {arc : Spec (of V) ⟶ X} [Field k] {ϑ : V →+* k} [IsLocalHom ϑ] (s : X ⟶ Spec R)
    [LocallyOfFiniteType s] [IsDomain R] [IsIntegrallyClosed R]
    (h_imm : IsHolomorphicImmersionAt φ w₀)
    (h_arc_extends : specMap V.subtype ≫ arc = φ w₀)
    (h_over : ∀ w : Fin d → ℂ, φ w ≫ s = Spec.map emb) (h_emb_inj : Function.Injective emb)
    (h_spec : ∀ᶠ w : Fin d → ℂ in nhds w₀, φ w₀ (closedPoint ℂ) ⤳ φ w (closedPoint ℂ))
    (h_tangent : ∀ (M : ModuleCat k) (τ : Spec (of (TrivSqZeroExt k (Dual k M))) ⟶ X),
      let t := specMap ϑ ≫ arc
      sqZeroReduction k (Dual k M) ≫ τ = t →
      τ ≫ s = specMap (algebraMap k (TrivSqZeroExt k (Dual k M))) ≫ t ≫ s →
      (∀ l : M,
        specMap (TrivSqZeroExt.map (Dual.eval k M l)).toRingHom ≫ τ =
          specMap (algebraMap k (TrivSqZeroExt k k)) ≫ t →
        l = 0) →
      Module.finrank k M ≤ d) :
    ∃ U : X.Opens, LandsIn arc U ∧ SmoothOfRelativeDimension d (U.ι ≫ s) := by
  have ⟨W, hW, hb⟩ := exists_isAffineOpen_landsIn arc
  let B := Γ(X, W)
  obtain ⟨⟨ρ, hρ⟩, α, rfl⟩ := map_surjective (hW.fromSpec ≫ s), landsIn_opensRange.1
    (hW.opensRange_fromSpec ▸ hb)
  have := Spec_iff.1 (hρ ▸ locallyOfFiniteType_comp ..)
  algebraize [ρ.hom, ϑ.comp α.1]
  have ⟨ι, x, _, hx, li⟩ := exists_linearIndependent' k (mk B k _ 1 ∘ D R B)
  simp [range_comp _ (D ..), ← Submodule.baseChange_span, span_range_derivation] at hx
  have ⟨i⟩ : #ι ≤ #(Fin d) := by grw [li.cardinalMk_le_finrank, ← Subspace.dual_finrank_eq,
    h_tangent (.of k _) (specMap {toFun w₀ := .inl (ϑ (α w₀)) + .inr (applyₗ (mk B k _ 1 (D R B
        w₀))), ..} ≫
    hW.fromSpec) _ _ fun l ↦ ext_on_range hx ∘ _] <;> simp [← hρ, ← Spec.map_comp, B,
    ← map_comp_assoc, cancel_mono, forall_and, TrivSqZeroExt.ext_iff, tmul_add,
    ← algebraMap_toAlgebra ρ.hom] <;> tauto
  obtain ⟨z, rfl⟩ := i.2.surjective_comp_right x
  let p := PrimeSpectrum.comap (algebraMap B k) ⊥
  let A := MvPolynomial (Fin d) R
  let e := mvPolynomialBasis R (Fin d)
  algebraize [(Ideal.ResidueField.liftₐ p.1 (ofId ..) le_rfl fun _ ↦ .mk0 _).1, (eval₂AlgHom R z).1]
  obtain ⟨hw, _, _, _ : IsIntegrallyClosed (MvPolynomial (Fin d) R)⟩ := h_arc_extends ▸ hb.comp _,
    FiniteType.of_restrictScalars_finiteType R A B, IsStandardSmooth.of_basis_kaehlerDifferential e
    (by rintro _ ⟨i, rfl⟩; exact ⟨.X i, by
      first | simp [e] | simp [e, mvPolynomialBasis] | exact (mvPolynomialBasis_apply ..).symm⟩),
    d.rec (.of_equiv (isEmptyRingEquiv ..).symm) fun _ _ ↦ .of_equiv
    (finSuccEquiv R _).symm.toRingEquiv
  have ⟨f, hf, C, π, hπ⟩ := (unramifiedLocus_eq_compl_support.ge (
    have := (mem_support_iff_nontrivial_residueField_tensorProduct p).1 ·
    have := (AlgebraTensorModule.cancelBaseChange B p.1.ResidueField k k Ω[B⁄A]).symm.nontrivial
    ne_zero_of_surjective (baseChange_surjective k (map_surjective R A _)) (ext_on_range hx (by
    simp [← (id (aeval_X ..) : algebraMap A B _ = _)]))) :
    IsUnramifiedAt A _).exists_hasStandardEtaleSurjectionOn
  obtain ⟨⟨β, rfl⟩ : ∃ β, ofHom (algebraMap B (Away f)) ≫ β = α, ⟨⟨G⟩⟩, r⟩ := ⟨_, hom_ext (lift_comp
    _ (.of_map ϑ _ (.mk0 _ hf)))⟩, instIsStandardEtaleRing C,
    (isRegularOn_ofSection · |> (h_imm.1 · hw))
  algebraize [β.1, β.1.comp (algebraMap A _)]
  have hx := (G.hasMap.map π).map (algHom _ _ V)
  with_unfolding_all have := (faithfulSMul_iff_algebraMap_injective A V).2 (.of_ker _ fun Q hQ ↦
   map_injective _ h_emb_inj (funext (eq_zero_of_submersion (.eval_mvPolynomial _)
   (hasStrictFDerivAt_pi.2 (z · |> r |>.2.hasStrictFDerivAt)) (ker_eq_bot_iff_range_eq_top.1
   (bot_unique fun v h0 ↦ h_imm.2 v ((h_imm.1.exists_isJet _).elim fun τ hτ ↦ by
   convert hτ
   obtain ⟨τ, rfl⟩ :=
     landsIn_opensRange.1 (hτ _ 0 (landsIn_opensRange.2 ⟨β ≫ _, by simpa using h_arc_extends⟩)).1
   algebraize [τ.hom.comp (algebraMap A _)]
   simpa [← hτ.fst_comp, specMap] using congr(specMap $((FormallyUnramified.of_surjective π hπ).ext'
     _ ⟨2, kerIdeal_sq ℂ ℂ⟩ ⟨(inlHom ..).comp ((fstHom ..).1.comp τ.hom), fun Q ↦ by
     have := And.intro (hτ.comp_base_eq h_over) (hτ W <| z ·)
     simp [← hρ, ← map_comp_assoc, ← Spec.map_comp, funext_iff] at this h0
     apply Q.induction_on <;> simp +contextual [A, algebraMap_toAlgebra, algebraMap_eq_inl,
       IsScalarTower.algebraMap_apply A B, *]⟩ ⟨τ.hom, by tauto⟩ (by tauto)).1 ≫ _))))
   ((r 0).1.mp (h_spec.mono fun w h_imm k ↦ by
   simpa [← (landsIn_iff_mem), landsIn_basicOpen, ofSection_eq, k,
     ← (map_injective (by simp [*, reassoc_of% map_evalSection_fromSpec]) : ρ ≫ evalSection _ k =
     emb)] using! mt (h_imm.mem_open (X.basicOpen (aeval z Q)).2)
     (h_arc_extends ▸ ((hW.fromSpec_preimage_basicOpen _).le · (·.ne_zero congr($hQ)))))))))
  have hm p := minpoly.isIntegrallyClosed_dvd (p := p) ⟨_, G.monic_f, hx.1⟩
  have ⟨g, h_spec⟩ := hm _ hx.1
  have := Etale.iff_isStandardSmoothOfRelativeDimension_zero.1 (.of_equiv (.ofBijective (awayMapₐ π
    _) ⟨awayMap_injective_iff.2 fun c (k : π c = 0) ↦ (G.exists_mul_aeval_x_g_pow_eq_aeval_x c).elim
    fun arc ⟨n, h_arc_extends⟩ ↦ ⟨1, by grw [← zero_dvd_iff, ← (G.hasMap.2.pow n).dvd_mul_right,
        mul_assoc, h_arc_extends,
    pow_one, ← map_mul, ← hm arc (by simp [arc.aeval_algHom_apply, ← h_arc_extends,
        k]), mul_comm, ← h_spec,
    G.hasMap.1]⟩, mapₐ_surjective_of_surjective _ hπ⟩))
  refine ⟨_, landsIn_opensRange (c := specMap (algebraMap ..) ≫ specMap (algebraMap _ (Away f)) ≫
    hW.fromSpec).2 ⟨ofHom (awayLift β.hom _ (by simpa [h_spec, g.aeval_algHom_apply] using!
    hx.isUnit_derivative_f : _ ∧ _).2), by rw [← map_comp_assoc, ← ofHom_comp]; simp⟩, ?_⟩
  simpa [← Scheme.Hom.isoOpensRange_inv_comp, ← hρ, ← Spec.map_comp] using comp_of_isOpenImmersion
    _ _ _ (Spec_iff.2 (locally_of isStandardSmoothOfRelativeDimension_respectsIso _ (by
    simpa [← isStandardSmoothOfRelativeDimension_algebraMap] using! ((iff_of_isStandardSmooth _).2
      (rank_eq_card_basis e)).trans _ 0 ..)))

end New
