/-
Copyright (c) 2026 Michał Świętek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Świętek
-/
module

public import Mathlib.Analysis.Normed.Module.SchauderBasis.Existence
public import Mathlib.Analysis.Normed.Module.SchauderBasis.CountablyCompact
public import Mathlib.Topology.Maps.Basic

/-!
# Eberlein–Šmulian Theorem

The Eberlein–Šmulian theorem states that in a Banach space, a weakly countably compact set
is weakly compact.

## Main Results

* `Eberlein_Smulian`: A weakly countably compact set in a Banach space is weakly compact.
-/

@[expose] public section

noncomputable section

open Submodule Set WeakDual Metric Filter Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

namespace BasicSequence

/-- From an injective function `σ : ℕ → ℕ`, extract a subsequence `ψ` such that
    both `ψ` and `σ ∘ ψ` are strictly monotone. -/
lemma exists_strictMono_comp_strictMono (σ : ℕ → ℕ) (hσ : Function.Injective σ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ StrictMono (σ ∘ ψ) := by
  have hσ_tendsto := hσ.nat_tendsto_atTop
  have h_exists : ∀ n : ℕ, ∃ k, n < k ∧ σ n < σ k := by
    intro n
    obtain ⟨M, hM⟩ := Filter.tendsto_atTop_atTop.mp hσ_tendsto (σ n + 1)
    exact ⟨max (n + 1) M, by omega, Nat.lt_of_succ_le (hM _ (le_max_right _ _))⟩
  let next (n : ℕ) : ℕ := (h_exists n).choose
  have h_next_gt (n : ℕ) : n < next n := (h_exists n).choose_spec.1
  have h_next_σ (n : ℕ) : σ n < σ (next n) := (h_exists n).choose_spec.2
  -- ψ(k) = next^k(0)
  let ψ : ℕ → ℕ := fun k => next^[k] 0
  exact ⟨ψ,
    strictMono_nat_of_lt_succ fun n => by
      simp only [ψ, Function.iterate_succ', Function.comp_def]; exact h_next_gt _,
    strictMono_nat_of_lt_succ fun n => by
      simp only [ψ, Function.comp_def, Function.iterate_succ']; exact h_next_σ _⟩

end BasicSequence

open BasicSequence

open scoped Pointwise in
theorem IsCountablyCompact.isVonNBounded
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    {A : Set E} (hA : IsCountablyCompact A) :
    Bornology.IsVonNBounded 𝕜 A := by
  by_contra h_not
  rw [Bornology.IsVonNBounded] at h_not
  push_neg at h_not
  obtain ⟨V, hV, habs⟩ := h_not
  obtain ⟨W, ⟨hW_nhds, hW_bal⟩, hWV⟩ := (nhds_basis_balanced 𝕜 E).mem_iff.mp hV
  have h_not_abs_W : ¬ Absorbs 𝕜 W A := fun h => habs (h.mono_left hWV)
  have h_freq := Filter.not_eventually.mp h_not_abs_W
  have h_extract : ∀ n : ℕ, ∃ a : 𝕜, (↑n + 1 : ℝ) ≤ ‖a‖ ∧ ∃ x ∈ A, x ∉ a • W := by
    intro n
    have := ((Filter.hasBasis_cobounded_norm (E := 𝕜)).frequently_iff).mp h_freq (↑n + 1) trivial
    obtain ⟨a, ha_norm, ha_not⟩ := this
    exact ⟨a, ha_norm, Set.not_subset.mp ha_not⟩
  choose a ha_norm x hx_mem hx_not using h_extract
  have ha_ne : ∀ n, a n ≠ 0 := by
    intro n hn
    have h := ha_norm n; simp [hn] at h; linarith [Nat.cast_nonneg' (α := ℝ) n]
  have hinv_not : ∀ n, (a n)⁻¹ • x n ∉ W := fun n => by
    rw [← Set.mem_smul_set_iff_inv_smul_mem₀ (ha_ne n)]; exact hx_not n
  obtain ⟨p, _, hp_cluster⟩ := hA x hx_mem
  -- By continuity of smul at (0, p): since 0 • p = 0 ∈ W
  have hcont : Filter.Tendsto (fun (cx : 𝕜 × E) => cx.1 • cx.2) (𝓝 0 ×ˢ 𝓝 p) (𝓝 0) := by
    have := (continuous_smul (M := 𝕜) (X := E)).continuousAt (x := (0, p))
    rwa [ContinuousAt, zero_smul, nhds_prod_eq] at this
  obtain ⟨U, hU_mem, S, hS_mem, hUS⟩ := Filter.mem_prod_iff.mp (hcont hW_nhds)
  -- (a n)⁻¹ → 0 since ‖a n‖ → ∞
  have h_inv_tendsto : Filter.Tendsto (fun n => (a n)⁻¹) Filter.atTop (𝓝 (0 : 𝕜)) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _)
      (fun n => by rw [norm_inv]; exact inv_anti₀ (by positivity) (ha_norm n))
      (tendsto_inv_atTop_zero.comp
        (Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ)
          tendsto_natCast_atTop_atTop))
  obtain ⟨n, hxS, haU⟩ := (hp_cluster.frequently hS_mem).and_eventually (h_inv_tendsto hU_mem)
    |>.exists
  exact hinv_not n (hUS (Set.mk_mem_prod haU hxS))

open scoped Pointwise in
theorem IsCountablyCompact_IsBounded
    (A : Set (WeakSpace 𝕜 X))
    (hA : IsCountablyCompact A) : Bornology.IsBounded ((toWeakSpace 𝕜 X).symm '' A) := by
  rw [isBounded_iff_forall_norm_le]
  have hVNB := hA.isVonNBounded (𝕜 := 𝕜)
  set S := (toWeakSpace 𝕜 X).symm '' A
  have h_ptwise : ∀ f : X →L[𝕜] 𝕜, ∃ C, ∀ (i : ↥S),
      ‖(NormedSpace.inclusionInDoubleDual 𝕜 X (↑i)) f‖ ≤ C := by
    intro f
    have hV_mem : (fun (x : WeakSpace 𝕜 X) => ((topDualPairing 𝕜 X).flip x) f) ⁻¹'
        (Metric.ball 0 1) ∈ 𝓝 (0 : WeakSpace 𝕜 X) :=
      (WeakBilin.eval_continuous _ f).continuousAt.preimage_mem_nhds
        (by simp [Metric.ball_mem_nhds])
    obtain ⟨r, hr_pos, hr_abs⟩ := (hVNB hV_mem).exists_pos
    obtain ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜 r
    have hc_ne : c ≠ 0 := norm_pos_iff.mp (hr_pos.trans hc)
    refine ⟨‖c‖, fun ⟨x, hx⟩ => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hx
    have hy_mem := hr_abs c (le_of_lt hc) hy
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc_ne] at hy_mem
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, map_smul,
      LinearMap.smul_apply, norm_smul, norm_inv] at hy_mem
    change ‖((topDualPairing 𝕜 X).flip y) f‖ ≤ ‖c‖
    linarith [inv_mul_lt_iff₀ (norm_pos_iff.mpr hc_ne) |>.mp hy_mem]
  -- Apply Banach-Steinhaus (uniform boundedness principle)
  obtain ⟨C, hC⟩ := banach_steinhaus h_ptwise
  refine ⟨C, fun x hx => ?_⟩
  have h := hC ⟨x, hx⟩
  exact NormedSpace.norm_le_dual_bound 𝕜 x
    ((ContinuousLinearMap.opNorm_nonneg _).trans h) fun f =>
    (((NormedSpace.inclusionInDoubleDual 𝕜 X) x).le_opNorm f).trans
      (mul_le_mul_of_nonneg_right h (norm_nonneg f))

theorem Eberlein_Smulian' [CompleteSpace X] (A : Set (WeakSpace 𝕜 X))
    (hA : IsCountablyCompact A) : IsSeqCompact A := by
  intro xn h_mem
  obtain ⟨x, hxA, hx_cluster⟩ := hA xn h_mem
  let xnX : ℕ → X := xn
  let xX : X := x
  by_cases h_sep : ∃ ε > 0, ∀ᶠ n in atTop, ε ≤ ‖xnX n - xX‖
  · -- Case B: x is NOT a norm cluster point (tail is ε-separated)
    obtain ⟨ε, hε, hev⟩ := h_sep
    obtain ⟨N, hN⟩ := hev.exists_forall_of_atTop
    let xn'X : ℕ → X := fun n => xnX (n + N)
    let S : Set X := Set.range (fun n => xn'X n - xX)
    have hS_ne : S.Nonempty := ⟨xn'X 0 - xX, Set.mem_range_self 0⟩
    have h_norm_0 : (0 : X) ∉ closure S := by
      intro h0
      rw [Metric.mem_closure_iff] at h0
      obtain ⟨y, hy, hd⟩ := h0 ε hε
      obtain ⟨n, rfl⟩ := hy
      rw [dist_comm, dist_eq_norm, sub_zero] at hd
      exact not_lt.mpr (hN (n + N) (Nat.le_add_left N n)) hd
    have h_weak_0 : (0 : X) ∈ closure (toWeakSpace 𝕜 X '' S) := by
      have h_tail_cluster : MapClusterPt x atTop (fun n => xn (n + N)) := by
        rw [show (fun n => xn (n + N)) = xn ∘ (· + N) from rfl, mapClusterPt_comp,
          map_add_atTop_eq_nat]
        exact hx_cluster
      have h_sub_cluster : MapClusterPt (0 : WeakSpace 𝕜 X) atTop
          (fun n => xn (n + N) - x) := by
        rw [show (0 : WeakSpace 𝕜 X) = x - x from (sub_self x).symm]
        exact (h_tail_cluster.continuousAt_comp
          (continuous_id.sub continuous_const).continuousAt)
      exact clusterPt_iff_forall_mem_closure.mp h_sub_cluster.clusterPt
        (toWeakSpace 𝕜 X '' S) (Filter.mem_map.mpr (Filter.Eventually.of_forall
          fun n => ⟨xn'X n - xX, Set.mem_range_self n, rfl⟩))
    -- Extract a basic sequence from S via weak/norm closure gap
    obtain ⟨e, he_mem, he_basic⟩ :=
      exists_basicSequence_of_weakClosure_not_normClosure h_norm_0 h_weak_0
    choose σ hσ using he_mem
    have he_inj : Function.Injective e :=
      he_basic.coe_toBasicSequence ▸ he_basic.toBasicSequence.injective
    have hσ_inj : Function.Injective σ := fun k₁ k₂ hk =>
      he_inj ((hσ k₁).symm.trans (hk ▸ hσ k₂))
    obtain ⟨ψ, hψ_mono, hσψ_mono⟩ := exists_strictMono_comp_strictMono σ hσ_inj
    let yn : ℕ → WeakSpace 𝕜 X := fun k => xn (σ k + N)
    have h_unique : ∀ y : WeakSpace 𝕜 X, MapClusterPt y atTop yn → y = x := by
      intro y hy_cluster
      rw [show yn = (fun k => toWeakSpace 𝕜 X (e k + xX)) from
        funext fun k => sub_eq_iff_eq_add.mp (hσ k)] at hy_cluster
      exact weakClusterPt_of_basicSequence_add he_basic xX hy_cluster
    have h_yn_tendsto : Tendsto yn atTop (𝓝 x) :=
      unique_clusterPt_limit A hA x yn (fun n => h_mem (σ n + N)) h_unique
    let φ : ℕ → ℕ := fun k => σ (ψ k) + N
    exact ⟨x, hxA, φ, fun _ _ hab => Nat.add_lt_add_right (hσψ_mono hab) N,
      h_yn_tendsto.comp hψ_mono.tendsto_atTop⟩
  · -- Case A: x IS a norm cluster point
    push_neg at h_sep
    have h_norm_cluster : MapClusterPt xX atTop xnX := by
      rw [mapClusterPt_iff_frequently]
      intro s hs
      rw [Metric.mem_nhds_iff] at hs
      obtain ⟨ε, hε, hball⟩ := hs
      exact (h_sep ε hε).mono fun n hn => hball (Metric.mem_ball.mpr (by rwa [dist_eq_norm]))
    obtain ⟨ψ, hψ_mono, hψ_tendsto⟩ :=
      TopologicalSpace.FirstCountableTopology.tendsto_subseq h_norm_cluster
    exact ⟨x, hxA, ψ, hψ_mono,
      (toWeakSpaceCLM 𝕜 X).continuous.continuousAt.tendsto.comp hψ_tendsto⟩

-- TODO add consequeces eg: Freshet-Uryshon, reflexivity of weak compactness, etc.
/-- **Eberlein–Šmulian theorem**: In a Banach space, a weakly countably compact set
is weakly compact. -/
theorem Eberlein_Smulian [CompleteSpace X] (A : Set (WeakSpace 𝕜 X))
    (hA : IsCountablyCompact A) : IsCompact A := by
  by_cases hA_ne : A.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.mp hA_ne]; exact isCompact_empty
  have h_bounded := IsCountablyCompact_IsBounded A hA
  let A_X : Set X := (toWeakSpace 𝕜 X).symm '' A
  have hA_X_eq : toWeakSpace 𝕜 X '' A_X = A := by
    change toWeakSpace 𝕜 X '' ((toWeakSpace 𝕜 X).symm '' A) = A
    rw [Set.image_image]; simp
  have hA_X_ne : A_X.Nonempty := hA_ne.image _
  -- needed for TC synthesis performance
  letI : NormedAddCommGroup (StrongDual 𝕜 X) := inferInstance
  letI : NormedSpace 𝕜 (StrongDual 𝕜 X) := inferInstance
  letI : NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 X)) := inferInstance
  letI : NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 X)) := inferInstance
  letI : CompleteSpace (StrongDual 𝕜 (StrongDual 𝕜 X)) := inferInstance
  let J := NormedSpace.inclusionInDoubleDual 𝕜 X
  let ι := fun x : WeakSpace 𝕜 X => StrongDual.toWeakDual (J x)
  have hJ_iso : ∀ y, ‖J y‖ = ‖y‖ := fun y =>
    (NormedSpace.inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)).norm_map y
  have hι_cont : Continuous ι :=
    (NormedSpace.inclusionInDoubleDual_isEmbedding_weak 𝕜 X).continuous
  have h_range_eq : Set.range ι = StrongDual.toWeakDual '' (J '' Set.univ) := by
    ext φ; constructor
    · rintro ⟨x, rfl⟩; exact ⟨J x, ⟨x, trivial, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, _, rfl⟩, rfl⟩; exact ⟨x, rfl⟩
  let S_bidual := J '' A_X
  let K := closure (StrongDual.toWeakDual '' S_bidual)
  have h_S_bidual_bounded : Bornology.IsBounded S_bidual := by
    obtain ⟨R, hR⟩ := isBounded_iff_subset_closedBall 0 |>.mp h_bounded
    exact (isBounded_iff_subset_closedBall 0).mpr ⟨R, fun y ⟨x, hxS, hx_eq⟩ => by
      rw [mem_closedBall, dist_zero_right, ← hx_eq, hJ_iso]
      exact mem_closedBall_zero_iff.mp (hR hxS)⟩
  have h_mem_iff : ∀ x : X, x ∈ A_X ↔ toWeakSpace 𝕜 X x ∈ A := fun x => by
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (toWeakSpace 𝕜 X).apply_symm_apply a ▸ ha
    · exact fun h => ⟨toWeakSpace 𝕜 X x, h, (toWeakSpace 𝕜 X).symm_apply_apply x⟩
  suffices hK : K ⊆ StrongDual.toWeakDual '' (J '' Set.univ) by
    have h_compact_cl := compactness_transfer_from_bidual A_X S_bidual rfl K rfl
      h_S_bidual_bounded hK
    rw [hA_X_eq] at h_compact_cl
    suffices h_cl_sub : closure A ⊆ A by
      rwa [h_cl_sub.antisymm subset_closure] at h_compact_cl
    intro x₀ hx₀
    let x₀_X : X := (toWeakSpace 𝕜 X).symm x₀
    have hx₀_eq : toWeakSpace 𝕜 X x₀_X = x₀ := (toWeakSpace 𝕜 X).apply_symm_apply x₀
    by_cases h_norm_x : x₀_X ∈ closure A_X
    · -- Case 1: x₀ in norm closure → extract norm-convergent sequence
      haveI : FrechetUrysohnSpace X := FirstCountableTopology.frechetUrysohnSpace
      obtain ⟨a, ha_mem, ha_lim⟩ := mem_closure_iff_seq_limit.mp h_norm_x
      have h_weak_lim : Filter.Tendsto (fun n => toWeakSpace 𝕜 X (a n)) atTop (𝓝 x₀) := by
        rw [← hx₀_eq]
        exact (toWeakSpaceCLM 𝕜 X).continuous.continuousAt.tendsto.comp ha_lim
      obtain ⟨y, hyA, hy_cp⟩ := hA _ (fun n => (h_mem_iff (a n)).mp (ha_mem n))
      exact (t2_iff_nhds.mp inferInstance (hy_cp.clusterPt.mono h_weak_lim)) ▸ hyA
    · -- Case 2: x₀ NOT in norm closure → basic sequence argument
      let S : Set X := (· - x₀_X) '' A_X
      have hS_ne : S.Nonempty := hA_X_ne.image _
      have h_norm_0 : (0 : X) ∉ closure S := by
        rw [show S = Homeomorph.addRight (-x₀_X) '' A_X from by ext y; simp [S, sub_eq_add_neg],
          ← (Homeomorph.addRight (-x₀_X)).image_closure]
        rintro ⟨z, hz, hze⟩
        exact h_norm_x ((add_neg_eq_zero.mp hze) ▸ hz)
      have h_weak_0 : (0 : X) ∈ closure (toWeakSpace 𝕜 X '' S) := by
        have h_eq : toWeakSpace 𝕜 X '' S =
            (Homeomorph.addRight (-x₀) : WeakSpace 𝕜 X ≃ₜ WeakSpace 𝕜 X) '' A := by
          ext w; constructor
          · rintro ⟨_, ⟨a, haX, rfl⟩, rfl⟩
            exact ⟨toWeakSpace 𝕜 X a, (h_mem_iff a).mp haX,
              by simp [Homeomorph.addRight, sub_eq_add_neg, hx₀_eq]⟩
          · rintro ⟨y, hyA, rfl⟩
            exact ⟨(toWeakSpace 𝕜 X).symm y - x₀_X,
              ⟨(toWeakSpace 𝕜 X).symm y,
                (h_mem_iff _).mpr ((toWeakSpace 𝕜 X).apply_symm_apply y ▸ hyA), rfl⟩,
              by simp [Homeomorph.addRight, sub_eq_add_neg, hx₀_eq]⟩
        rw [h_eq, ← (Homeomorph.addRight (-x₀ : WeakSpace 𝕜 X)).image_closure]
        exact ⟨x₀, hx₀, by simp [Homeomorph.addRight]⟩
      obtain ⟨e, he_mem, he_basic⟩ :=
        exists_basicSequence_of_weakClosure_not_normClosure h_norm_0 h_weak_0
      choose σ hσ_mem hσ_eq using fun n => he_mem n
      obtain ⟨y, hyA, hy_cp⟩ := hA (fun n => toWeakSpace 𝕜 X (σ n))
        (fun n => (h_mem_iff (σ n)).mp (hσ_mem n))
      rw [show (fun n => toWeakSpace 𝕜 X (σ n)) = (fun n => toWeakSpace 𝕜 X (e n + x₀_X)) from
        funext fun n => congrArg _ (sub_eq_iff_eq_add.mp (hσ_eq n))] at hy_cp
      exact (weakClusterPt_of_basicSequence_add he_basic x₀_X hy_cp).trans hx₀_eq ▸ hyA
  by_contra h_not_subset
  rw [Set.subset_def] at h_not_subset; push_neg at h_not_subset
  obtain ⟨w, hwK, hw_not_range⟩ := h_not_subset
  have hw_not_range_ι : w ∉ Set.range ι := by rwa [h_range_eq]
  let w' : StrongDual 𝕜 (StrongDual 𝕜 X) := WeakDual.toStrongDual w
  have hw'_not_range : w' ∉ Set.range J := by
    intro ⟨x, hx⟩; apply hw_not_range_ι
    exact ⟨x, show StrongDual.toWeakDual (J x) = w by
      rw [hx]; exact LinearEquiv.apply_symm_apply StrongDual.toWeakDual w⟩
  have hw'_ne : w' ≠ 0 := fun h => hw'_not_range ⟨0, show J 0 = w' by rw [map_zero, h]⟩
  have ⟨f₀, hf₀⟩ : ∃ f₀ : StrongDual 𝕜 X, w' f₀ ≠ 0 := by
    by_contra h; push_neg at h
    exact hw'_ne (ContinuousLinearMap.ext fun g => h g)
  let c := w' f₀
  have hc_ne : c ≠ 0 := hf₀
  let f : StrongDual 𝕜 X := (2 * c⁻¹) • f₀
  have hf_val : w' f = 2 := by
    simp only [f, map_smul, smul_eq_mul, show w' f₀ = c from rfl,
      mul_assoc, inv_mul_cancel₀ hc_ne, mul_one]
  have hf_norm : 1 < ‖w' f‖ := by rw [hf_val, RCLike.norm_ofNat]; norm_num
  have h_sep_open : IsOpen {φ : WeakDual 𝕜 (StrongDual 𝕜 X) | 1 < ‖φ f‖} :=
    isOpen_lt continuous_const (continuous_norm.comp (WeakBilin.eval_continuous _ f))
  have hw_in_sep : w ∈ {φ : WeakDual 𝕜 (StrongDual 𝕜 X) | 1 < ‖φ f‖} := hf_norm
  let A₀ : Set X := {x ∈ A_X | 1 < ‖f x‖}
  have hA₀_ne : A₀.Nonempty := by
    obtain ⟨z, hz_sep, hz_mem⟩ :=
      mem_closure_iff_nhds.mp hwK _ (h_sep_open.mem_nhds hw_in_sep)
    obtain ⟨_, ⟨x, hxA, rfl⟩, rfl⟩ := hz_mem
    exact ⟨x, hxA, hz_sep⟩
  have hA₀_bounded : Bornology.IsBounded A₀ := h_bounded.subset (fun _ hx => hx.1)
  have h_not_compact : ¬ IsCompact (closure (toWeakSpace 𝕜 X '' A₀)) := by
    intro h_compact
    have hιC_closed := (h_compact.image hι_cont).isClosed
    have h_ι_A₀ : StrongDual.toWeakDual '' (J '' A₀) = ι '' (toWeakSpace 𝕜 X '' A₀) := by
      ext φ; constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨_, mem_image_of_mem _ hx, rfl⟩
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hw_in_cl : w ∈ closure (ι '' (toWeakSpace 𝕜 X '' A₀)) := by
      rw [← h_ι_A₀, mem_closure_iff_nhds]; intro U hU
      obtain ⟨z, ⟨hzU, hz_sep⟩, hz_mem⟩ :=
        mem_closure_iff_nhds.mp hwK _ (Filter.inter_mem hU (h_sep_open.mem_nhds hw_in_sep))
      obtain ⟨_, ⟨x, hxA, rfl⟩, rfl⟩ := hz_mem
      exact ⟨StrongDual.toWeakDual (J x), hzU, J x, ⟨x, ⟨hxA, hz_sep⟩, rfl⟩, rfl⟩
    obtain ⟨y, _, rfl⟩ := closure_minimal (Set.image_mono subset_closure) hιC_closed hw_in_cl
    exact hw_not_range_ι ⟨y, rfl⟩
  obtain ⟨e, he_mem, he_basic⟩ : ∃ (e : ℕ → X), (∀ n, e n ∈ A₀) ∧ IsBasicSequence 𝕜 e := by
    by_contra h_no; push_neg at h_no
    exact h_not_compact
      (no_basic_sequence_implies_relatively_weakly_compact hA₀_ne hA₀_bounded h_no)
  obtain ⟨a, _, ha_cluster⟩ := hA (fun n => (toWeakSpace 𝕜 X) (e n))
    (fun n => (h_mem_iff (e n)).mp (he_mem n).1)
  have ha_eq_0 : a = 0 :=
    (weakClusterPt_of_basicSequence_add he_basic 0 (by simpa using ha_cluster)).trans (map_zero _)
  have h_cluster_f : MapClusterPt (0 : 𝕜) atTop (fun n => f (e n)) := by
    have := (WeakBilin.eval_continuous (topDualPairing 𝕜 X).flip f).continuousAt
      |> ha_cluster.continuousAt_comp
    simp only [ha_eq_0, map_zero, LinearMap.zero_apply] at this; exact this
  obtain ⟨n, hn⟩ := (h_cluster_f.frequently (ball_mem_nhds 0 one_pos)).exists
  exact absurd (dist_zero_right (f (e n)) ▸ hn) (not_lt.mpr (le_of_lt (he_mem n).2))

/-- Weakly compact subsets of a Banach space are Fréchet-Urysohn in the subspace topology.
This is the "angelic" property of weakly compact sets: in a weakly compact set, closure
equals sequential closure. -/
theorem IsCompact.frechetUrysohnSpace [CompleteSpace X]
    {K : Set (WeakSpace 𝕜 X)} (hK : IsCompact K) :
    FrechetUrysohnSpace K := by
  have hK_cc : IsCountablyCompact K := IsCompact_IsCountablyCompact hK
  constructor
  intro s a ha_cl
  rw [closure_subtype] at ha_cl
  set S_W : Set (WeakSpace 𝕜 X) := Subtype.val '' s
  set x₀ : X := (toWeakSpace 𝕜 X).symm ↑a
  set S_X : Set X := (toWeakSpace 𝕜 X).symm '' S_W
  have hx₀_eq : toWeakSpace 𝕜 X x₀ = ↑a := (toWeakSpace 𝕜 X).apply_symm_apply ↑a
  by_cases hS_ne : S_X.Nonempty
  swap
  · exfalso; rw [Set.not_nonempty_iff_eq_empty] at hS_ne
    have : S_W = ∅ := by
      have : S_X = ∅ := hS_ne
      rw [show S_W = toWeakSpace 𝕜 X '' S_X from by simp [S_X, Set.image_image],
        this, Set.image_empty]
    rw [this, closure_empty] at ha_cl; exact ha_cl
  have h_img_eq : toWeakSpace 𝕜 X '' S_X = S_W := by simp [S_X, Set.image_image]
  have h_S_W_sub_K : S_W ⊆ K := fun _ ⟨k, _, hk⟩ => hk ▸ k.property
  by_cases h_norm : x₀ ∈ closure S_X
  · -- Case 1: x₀ in norm closure → norm-convergent sequence
    haveI : FrechetUrysohnSpace X := FirstCountableTopology.frechetUrysohnSpace
    obtain ⟨σ, hσ_mem, hσ_lim⟩ := mem_closure_iff_seq_limit.mp h_norm
    have h_weak_lim : Tendsto (fun n => toWeakSpace 𝕜 X (σ n)) atTop
        (𝓝 (↑a : WeakSpace 𝕜 X)) := by
      rw [← hx₀_eq]
      exact (toWeakSpaceCLM 𝕜 X).continuous.continuousAt.tendsto.comp hσ_lim
    have h_in_S_W : ∀ n, toWeakSpace 𝕜 X (σ n) ∈ S_W := by
      intro n; rw [← h_img_eq]; exact Set.mem_image_of_mem _ (hσ_mem n)
    choose t ht_mem ht_val using h_in_S_W
    exact ⟨t, ht_mem, Topology.IsInducing.subtypeVal.tendsto_nhds_iff.mpr
      (h_weak_lim.congr fun n => (ht_val n).symm)⟩
  · -- Case 2: x₀ not in norm closure → basic sequence argument
    let S' : Set X := (· - x₀) '' S_X
    have hS'_ne : S'.Nonempty := hS_ne.image _
    have h_norm_0 : (0 : X) ∉ closure S' := by
      rw [show S' = Homeomorph.addRight (-x₀) '' S_X from by ext y; simp [S', sub_eq_add_neg],
        ← (Homeomorph.addRight (-x₀)).image_closure]
      rintro ⟨z, hz, hze⟩
      exact h_norm ((add_neg_eq_zero.mp hze) ▸ hz)
    have h_weak_0 : (0 : X) ∈ closure (toWeakSpace 𝕜 X '' S') := by
      have h_eq : toWeakSpace 𝕜 X '' S' =
          (Homeomorph.addRight (-(↑a : WeakSpace 𝕜 X)) :
            WeakSpace 𝕜 X ≃ₜ WeakSpace 𝕜 X) '' S_W := by
        ext w; constructor
        · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
          obtain ⟨w', hw', rfl⟩ := hz
          exact ⟨w', hw', by simp [Homeomorph.addRight, sub_eq_add_neg, hx₀_eq]⟩
        · rintro ⟨w', hw', rfl⟩
          refine ⟨(toWeakSpace 𝕜 X).symm w' - x₀,
            ⟨(toWeakSpace 𝕜 X).symm w', Set.mem_image_of_mem _ hw', rfl⟩,
            by simp [Homeomorph.addRight, sub_eq_add_neg, hx₀_eq]⟩
      rw [h_eq, ← (Homeomorph.addRight (-(↑a : WeakSpace 𝕜 X))).image_closure]
      exact ⟨↑a, ha_cl, by simp [Homeomorph.addRight]⟩
    obtain ⟨e, he_mem, he_basic⟩ :=
      exists_basicSequence_of_weakClosure_not_normClosure h_norm_0 h_weak_0
    have h_in_S_W : ∀ n, toWeakSpace 𝕜 X (e n + x₀) ∈ S_W := by
      intro n
      obtain ⟨z, hz, hze⟩ := he_mem n
      rw [← h_img_eq]; exact ⟨e n + x₀, (sub_eq_iff_eq_add.mp hze) ▸ hz, rfl⟩
    choose t ht_mem ht_val using h_in_S_W
    have h_unique : ∀ y : WeakSpace 𝕜 X,
        MapClusterPt y atTop (fun n => (↑(t n) : WeakSpace 𝕜 X)) → y = ↑a := by
      intro y hy
      rw [show (fun n => (↑(t n) : WeakSpace 𝕜 X)) = fun n => toWeakSpace 𝕜 X (e n + x₀) from
        funext fun n => ht_val n] at hy
      exact (weakClusterPt_of_basicSequence_add he_basic x₀ hy).trans hx₀_eq
    have h_tendsto : Tendsto (fun n => (↑(t n) : WeakSpace 𝕜 X)) atTop
        (𝓝 (↑a : WeakSpace 𝕜 X)) :=
      let a_w : WeakSpace 𝕜 X := ↑a
      unique_clusterPt_limit K hK_cc a_w (fun n => ↑(t n))
        (fun n => (t n).property) h_unique
    exact ⟨t, ht_mem, Topology.IsInducing.subtypeVal.tendsto_nhds_iff.mpr h_tendsto⟩

theorem Reflexive_iff_ball_seqCompact [CompleteSpace X] :
    Module.IsReflexive 𝕜 X ↔ IsSeqCompact (Metric.closedBall (0 : X) 1) := sorry

def IsCountablyTight {E : Type*} [TopologicalSpace E] (A : Set E) : Prop :=
  ∀ x ∈ closure A, ∃ S ⊆ A, S.Countable ∧ x ∈ closure S

class CountablyTight (E : Type*) [TopologicalSpace E] : Prop where
  isCountablyTight : ∀ A : Set E, IsCountablyTight A

theorem Compact.CountablyTight [CompleteSpace X] {K : Set (WeakSpace 𝕜 X)} (hK : IsCompact K) :
    CountablyTight K := by
  have : FrechetUrysohnSpace K := hK.frechetUrysohnSpace
  constructor
  intro A x hx
  rw [mem_closure_iff_seq_limit] at hx
  obtain ⟨u, hu_mem, hu_lim⟩ := hx
  exact ⟨Set.range u, Set.range_subset_iff.mpr hu_mem, Set.countable_range u,
    mem_closure_of_tendsto hu_lim (Filter.eventually_of_forall Set.mem_range_self)⟩
