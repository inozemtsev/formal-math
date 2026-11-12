module

public import Green64.Library.Weights.NumericRestrictedPool
public import Green64.Library.Correlation.Part031

@[expose] public section

/-!
# Weights / Part061

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalActualBackgroundGroup -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 18000000
variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]

/-- The literal source G coefficient and carrier on a background subset,
at rho=1. The source endpoint eta and q are retained exactly. -/
theorem source_original_ACTUAL_BACKGROUND_group_G434
    (B : Finset P) (pending : Multiset (Atom P modulus))
    (q : ℝ) (N i : ℕ) (V : ℝ) (mu : P → ℝ) (seen : Finset ℕ)
    (F : Multiset (Atom P modulus) → Finset ℕ → ℂ) :
    (∑ d : SourceOriginalRestrictedPrimeBirthChoice434 modulus
      ((pending.toFinset.filter (fun z => z.2=0)).filter (fun z => z.1 ∈ B))
      (Finset.univ.filter (fun p => p ∈ B)),
      (if ∀ p ∈ d.2.1,modulus p ∉ seen then
        sourceOriginalGroupPrimeBirthWeight434 modulus
          ((pending.toFinset.filter (fun z => z.2=0)).filter (fun z => z.1 ∈ B))
          (-((sourceVisitEta q N i:ℝ):ℂ)/(1:ℂ))
          (((sourceVisitQ q N i:ℝ):ℂ)/(1:ℂ)^2)
          (-((sourceVisitEta q N i:ℝ):ℂ)*(V:ℂ)/(1:ℂ))
          (fun p => (mu p:ℂ)) (sourceOriginalRestrictedPrimeBirthLift434 modulus _ _ d)
        else 0) *
      F (sourceOriginalGhostPiecePending434 modulus
        (pending.toFinset.filter (fun z => z.1 ∈ B)) d.1.1 d.2.1)
        (seen ∪ d.2.1.image modulus)) =
    sourceOriginalPhysicalNumericRestrictedPoolG434 modulus B
      (sourceVisitEta q N i) V mu
      (pending.filter (fun z => z.1 ∈ B)) seen F := by
  have hB : Finset.univ.filter (fun p => p ∈ B)=B := by ext p; simp
  have hZ : ((pending.filter (fun z => z.1 ∈ B)).toFinset.filter (fun z => z.2=0)) =
      ((pending.toFinset.filter (fun z => z.2=0)).filter (fun z => z.1 ∈ B)) := by
    ext z
    simp only [Finset.mem_filter,Multiset.mem_toFinset,Multiset.mem_filter]
    tauto
  have hP : (pending.filter (fun z => z.1 ∈ B)).toFinset =
      pending.toFinset.filter (fun z => z.1 ∈ B) := by ext z; simp
  have hq : ((sourceVisitQ q N i:ℝ):ℂ)=1-((sourceVisitEta q N i:ℝ):ℂ) := by
    simp [sourceVisitEta]
  let e :
      SourceOriginalRestrictedPrimeBirthChoice434 modulus
        ((pending.toFinset.filter (fun z => z.2=0)).filter (fun z => z.1 ∈ B))
        (Finset.univ.filter (fun p => p ∈ B)) ≃
      SourceOriginalRestrictedPrimeBirthChoice434 modulus
        ((pending.filter (fun z => z.1 ∈ B)).toFinset.filter (fun z => z.2=0)) B :=
    { toFun := fun d =>
        (⟨d.1.1,by simpa only [hZ] using d.1.2⟩,
         ⟨d.2.1,by simpa only [hB] using d.2.2⟩)
      invFun := fun d =>
        (⟨d.1.1,by simpa only [hZ] using d.1.2⟩,
         ⟨d.2.1,by simpa only [hB] using d.2.2⟩)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold sourceOriginalPhysicalNumericRestrictedPoolG434
  apply Fintype.sum_equiv e
  intro d
  dsimp only [e,Equiv.coe_fn_mk,sourceOriginalGroupPrimeBirthWeight434,
    sourceOriginalRestrictedPrimeBirthLift434]
  simp only [hZ]
  simp only [hP,div_one,one_pow,hq,ite_mul,zero_mul]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalNumericBackgroundChain -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 18000000
variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]

theorem source_original_BACKGROUND_numeric_seen_strip434
    (B seen : Finset P) (hs : seen ⊆ B) (external : Finset ℕ)
    (hext : ∀ p ∈ B,modulus p ∉ external) :
    (external ∪ seen.image modulus) ∩ B.image modulus = seen.image modulus := by
  ext n
  constructor
  · intro h
    rcases Finset.mem_inter.mp h with ⟨h,hB⟩
    rcases Finset.mem_union.mp h with h|h
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hB
      exact False.elim (hext p hp h)
    · exact h
  · intro h
    exact Finset.mem_inter.mpr ⟨Finset.mem_union.mpr (Or.inr h),
      Finset.image_mono modulus hs h⟩

/-- Literal numerical birth gates on B, with an arbitrary changing
external seen schedule disjoint from B. Each mask observes both full
numerical seen states and all physical pending atoms. -/
def sourceOriginalPhysicalNumericBackgroundChain434
    (B : Finset P) (external : ℕ → Finset ℕ) (V : ℝ) (mu : P → ℝ)
    (mask : ℕ → Multiset (Atom P modulus) → Finset ℕ →
      Multiset (Atom P modulus) → Finset ℕ → ℂ) :
    List (ℝ × ℤ) → ℕ → (Multiset (Atom P modulus) → Finset ℕ → ℂ) →
      Multiset (Atom P modulus) → Finset ℕ → ℂ
  | [],_,F => F
  | v::vs,start,F => fun pending seen =>
      sourceOriginalPhysicalNumericRestrictedPoolG434 modulus B v.1 V mu pending seen
        (fun out st =>
          let nextSeen := external (start+1) ∪ (st ∩ B.image modulus)
          mask start pending seen (out.map (translateAtom v.2)) nextSeen *
          sourceOriginalPhysicalNumericBackgroundChain434 B external V mu mask vs
            (start+1) F (out.map (translateAtom v.2)) nextSeen)

/-- A continuation bound is needed only on the true background sector:
all other return states have exactly zero signed kernel coefficient. -/
theorem source_original_BACKGROUND_RETURN_supported_majorant434
    (B : Finset P) (shift : ℤ) (s : SourceOriginalPrimeReturnProductState434 modulus)
    (hs : ∀ p,p ∉ B → s p=.retired)
    (eta V : ℝ) (mu : P → ℝ)
    (he : 0 ≤ eta) (he1 : eta ≤ 1) (hl : ∀ p,0 ≤ V*mu p)
    (F : SourceOriginalPrimeReturnProductState434 modulus → ℂ)
    (G : (p : P) → SourceOriginalGhostReturnState434 (ZMod (modulus p)) → ℝ)
    (hG : ∀ p t,0 ≤ G p t)
    (hFG : ∀ t,(∀ p,p ∉ B → t p=.retired) → ‖F t‖ ≤ ∏ p,G p (t p)) :
    ‖sourceOriginalPrimeProductReturnRow434 modulus shift s eta V mu F‖ ≤
      ∏ p,sourceOriginalGhostReturnPositiveRow434 (-(shift : ZMod (modulus p)))
        eta (V*mu p) (G p) (s p) := by
  let F' := fun t => if ∀ p,p ∉ B → t p=.retired then F t else 0
  rw [source_original_BACKGROUND_RETURN_row_congr434 modulus B shift s hs eta V mu F F'
    (fun t ht => (if_pos ht).symm)]
  apply source_original_PRIME_PRODUCT_return_row_majorant434 modulus shift s eta V mu
    he he1 hl F' G hG
  intro t
  by_cases ht : ∀ p,p ∉ B → t p=.retired
  · simpa only [F',if_pos ht] using hFG t ht
  · simp only [F',if_neg ht,norm_zero]
    exact Finset.prod_nonneg (fun p hp => hG p (t p))

/-- Actual restricted numerical G/translation chain. Its external seen
may change at every visit. Arbitrary joint masks and terminal seen
tests are retained; no independence of them is asserted. -/
theorem source_original_NUMERIC_BACKGROUND_CHAIN_vacuum_majorant434
    (B : Finset P) (hi : Function.Injective modulus)
    (external : ℕ → Finset ℕ) (hext : ∀ i p,p ∈ B → modulus p ∉ external i)
    (V : ℝ) (mu : P → ℝ) (hl : ∀ p,0 ≤ V*mu p)
    (mask : ℕ → Multiset (Atom P modulus) → Finset ℕ →
      Multiset (Atom P modulus) → Finset ℕ → ℂ)
    (hm : ∀ i old seen out st,‖mask i old seen out st‖ ≤ 1)
    (vs : List (ℝ × ℤ)) (he : ∀ v ∈ vs,0 ≤ v.1 ∧ v.1 ≤ 1)
    (H : Finset ℕ → ℂ) (hH : ∀ st,‖H st‖ ≤ 1)
    (shift : ℤ) (start : ℕ) (s : SourceOriginalPrimeReturnProductState434 modulus)
    (hs : ∀ p,p ∉ B → s p=.retired) :
    ‖sourceOriginalPhysicalNumericBackgroundChain434 modulus B external V mu mask vs start
      (fun pending seen => if pending=0 then H seen else 0)
      (sourceOriginalPrimeProductPending434 modulus shift s)
      (external start ∪ (sourceOriginalPrimeProductSeen434 modulus s ∩ B).image modulus)‖ ≤
    ∏ p,sourceOriginalGhostReturnPositiveChain434
      (sourceOriginalSinglePrimeVisits434 modulus p shift vs) (V*mu p)
      sourceOriginalGhostReturnVacuum434 (s p) := by
  induction vs generalizing shift start s with
  | nil =>
      exact source_original_PRIME_PRODUCT_joint_vacuum_majorant434 modulus shift s
        (fun st => H (external start ∪ (st ∩ B).image modulus)) (fun st => hH _)
  | cons v vs ih =>
      have hv := he v List.mem_cons_self
      have ht := fun w hw => he w (List.mem_cons_of_mem v hw)
      dsimp only [sourceOriginalPhysicalNumericBackgroundChain434,
        sourceOriginalSinglePrimeVisits434,sourceOriginalGhostReturnPositiveChain434]
      rw [source_original_NUMERIC_BACKGROUND_POOL_G_return_matrix434 modulus B shift s hs
        hi (external start) (hext start)]
      apply source_original_BACKGROUND_RETURN_supported_majorant434 modulus B shift s hs
        v.1 V mu hv.1 hv.2 hl
      · intro p t
        apply source_original_RETURN_positive_chain_nonneg434 _ (V*mu p) (hl p)
        · exact source_original_PHYSICAL_SINGLE_PRIME_visits_unit434 modulus p vs ht (shift+v.2)
        · intro u
          cases u <;> simp [sourceOriginalGhostReturnVacuum434]
      · intro t hts
        rw [norm_mul]
        apply le_trans (mul_le_mul_of_nonneg_right (hm _ _ _ _ _) (norm_nonneg _))
        rw [one_mul,source_original_PRIME_PRODUCT_translate434,
          source_original_BACKGROUND_numeric_seen_strip434 modulus B
            (sourceOriginalPrimeProductSeen434 modulus t ∩ B) Finset.inter_subset_right
            (external start) (hext start)]
        exact ih ht (shift+v.2) (start+1) t hts
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalNumericBackgroundBaseline -/

section

open scoped BigOperators Classical
open Filter
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 18000000
variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]

/-- Only primes in the actual background pool are charged a baseline.
The full numerical seen observable and the changing external seen
schedule remain inside the literal chain. -/
theorem source_original_NUMERIC_BACKGROUND_CHAIN_baseline434
    (B : Finset P) (hi : Function.Injective modulus)
    (external : ℕ → Finset ℕ) (hext : ∀ i p,p ∈ B → modulus p ∉ external i)
    (V : ℝ) (mu : P → ℝ) (vs : List (ℝ × ℤ)) (shift : ℤ)
    (he : ∀ v ∈ vs,0 ≤ v.1 ∧ v.1 ≤ 1)
    (hb : ∀ p,0 < 1-(vs.map Prod.fst).sum/(modulus p:ℝ))
    (hlam : ∀ p,V*mu p = 1/((modulus p:ℝ)*(1-(vs.map Prod.fst).sum/(modulus p:ℝ))))
    (mask : ℕ → Multiset (Atom P modulus) → Finset ℕ →
      Multiset (Atom P modulus) → Finset ℕ → ℂ)
    (hm : ∀ i old seen out st,‖mask i old seen out st‖ ≤ 1)
    (start : ℕ) (H : Finset ℕ → ℂ) (hH : ∀ st,‖H st‖ ≤ 1) :
    ‖(∏ p ∈ B,((1-(vs.map Prod.fst).sum/(modulus p:ℝ):ℝ):ℂ)) *
      sourceOriginalPhysicalNumericBackgroundChain434 modulus B external V mu mask vs start
        (fun pending seen => if pending=0 then H seen else 0) 0 (external start)‖ ≤ 1 := by
  let s₀ : SourceOriginalPrimeReturnProductState434 modulus :=
    fun p => if p ∈ B then .unborn else .retired
  let b : P → ℝ := fun p => 1-(vs.map Prod.fst).sum/(modulus p:ℝ)
  let A : P → ℝ := fun p => sourceOriginalGhostReturnPositiveChain434
    (sourceOriginalSinglePrimeVisits434 modulus p shift vs) (V*mu p)
    sourceOriginalGhostReturnVacuum434 (s₀ p)
  have hl (p : P) : 0 ≤ V*mu p := by
    have hp : (0:ℝ) < modulus p := by exact_mod_cast NeZero.pos (modulus p)
    have hb' := hb p
    rw [hlam p]
    positivity
  have hA (p : P) : 0 ≤ A p := by
    apply source_original_RETURN_positive_chain_nonneg434 _ _ (hl p)
      (source_original_PHYSICAL_SINGLE_PRIME_visits_unit434 modulus p vs he shift)
    intro t
    cases t <;> simp [sourceOriginalGhostReturnVacuum434]
  have hs : ∀ p,p ∉ B → s₀ p=.retired := by
    intro p hp
    simp only [s₀,if_neg hp]
  have hpend : sourceOriginalPrimeProductPending434 modulus shift s₀=0 := by
    unfold sourceOriginalPrimeProductPending434
    apply Finset.sum_eq_zero
    intro p hp
    by_cases h : p ∈ B <;> simp [s₀,h,sourceOriginalOnePrimePending434]
  have hseen : sourceOriginalPrimeProductSeen434 modulus s₀ ∩ B = ∅ := by
    ext p
    simp only [Finset.mem_inter]
    constructor
    · intro ⟨hps,hpB⟩
      rw [source_original_PRIME_PRODUCT_seen_mem434] at hps
      simp [s₀,hpB,sourceOriginalOnePrimeSeen434] at hps
    · simp
  have hn := source_original_NUMERIC_BACKGROUND_CHAIN_vacuum_majorant434 modulus B hi
    external hext V mu hl mask hm vs he H hH shift start s₀ hs
  rw [hpend,hseen,Finset.image_empty,Finset.union_empty] at hn
  have haout (p : P) (hp : p ∉ B) : A p=1 := by
    dsimp only [A]
    rw [hs p hp]
    exact (source_original_GHOST_RETURN_positive_vacuum434 _ _).1
  have hprod : (∏ p,A p) = ∏ p ∈ B,A p := by
    symm
    apply Finset.prod_subset (Finset.subset_univ B)
    intro p hp hn
    exact haout p hn
  have hu (p : P) (hp : p ∈ B) : b p*A p ≤ 1 := by
    have h := (source_original_GHOST_RETURN_BASELINE_unit434
      (sourceOriginalSinglePrimeVisits434 modulus p shift vs)
      (source_original_PHYSICAL_SINGLE_PRIME_visits_unit434 modulus p vs he shift)
      (by simpa only [ZMod.card,source_original_PHYSICAL_SINGLE_PRIME_visits_sum434]
        using ne_of_gt (hb p))).2
    rw [(source_original_GHOST_RETURN_chain_exact434
      (sourceOriginalSinglePrimeVisits434 modulus p shift vs) _).2.2] at h
    simp only [ZMod.card,source_original_PHYSICAL_SINGLE_PRIME_visits_sum434] at h
    rw [←hlam p] at h
    dsimp only [b,A,s₀]
    rw [if_pos hp,(source_original_GHOST_RETURN_positive_vacuum434
      (sourceOriginalSinglePrimeVisits434 modulus p shift vs) (V*mu p)).2.2]
    exact h
  change ‖(∏ p ∈ B,(b p:ℂ)) * _‖ ≤ 1
  calc
    _ = (∏ p ∈ B,b p) * ‖sourceOriginalPhysicalNumericBackgroundChain434 modulus B
        external V mu mask vs start
        (fun pending seen => if pending=0 then H seen else 0) 0 (external start)‖ := by
      rw [norm_mul,norm_prod]
      congr 1
      apply Finset.prod_congr rfl
      intro p hp
      simp only [Complex.norm_real,Real.norm_eq_abs]
      exact abs_of_nonneg (show 0 ≤ b p from (hb p).le)
    _ ≤ (∏ p ∈ B,b p)*(∏ p,A p) :=
      mul_le_mul_of_nonneg_left hn (Finset.prod_nonneg (fun p hp => (hb p).le))
    _ = (∏ p ∈ B,b p)*(∏ p ∈ B,A p) := by rw [hprod]
    _ = ∏ p ∈ B,b p*A p := (Finset.prod_mul_distrib).symm
    _ ≤ ∏ p ∈ B,(1:ℝ) := Finset.prod_le_prod₀
      (fun p hp => mul_nonneg (hb p).le (hA p)) (fun p hp => hu p hp)
    _ = 1 := by simp

section Source
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]

theorem source_original_PHYSICAL_SOURCE_BACKGROUND_CHAIN_envelope434
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ) (V : BG → ℝ)
    (g : BG) (hV : V g ≠ 0) (hi : Function.Injective (bm g))
    (B : Finset (BP g)) (external : ℕ → Finset ℕ)
    (hext : ∀ i p,p ∈ B → bm g p ∉ external i)
    (hb : ∀ p,0 < physicalSourceBaseline BP bm q N g p)
    (steps : ℕ → ℤ)
    (mask : ℕ → Multiset (Atom (BP g) (bm g)) → Finset ℕ →
      Multiset (Atom (BP g) (bm g)) → Finset ℕ → ℂ)
    (hm : ∀ i old seen out st,‖mask i old seen out st‖ ≤ 1)
    (H : Finset ℕ → ℂ) (hH : ∀ st,‖H st‖ ≤ 1) :
    ‖(∏ p ∈ B,(physicalSourceBaseline BP bm q N g p:ℂ)) *
      sourceOriginalPhysicalNumericBackgroundChain434 (bm g) B external (V g)
        (physicalSourceMuTilde BP bm q N V g) mask
        (sourceOriginalPhysicalSourceStepVisits434 q N steps) 0
        (fun pending seen => if pending=0 then H seen else 0) 0 (external 0)‖ ≤ 1 := by
  have hlam (p : BP g) : V g*physicalSourceMuTilde BP bm q N V g p =
      1/((bm g p:ℝ)*physicalSourceBaseline BP bm q N g p) := by
    have hp : (bm g p:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne (bm g p)
    unfold physicalSourceMuTilde
    field_simp [hV,hp,ne_of_gt (hb p)]
  have h := source_original_NUMERIC_BACKGROUND_CHAIN_baseline434
    (bm g) B hi external hext (V g) (physicalSourceMuTilde BP bm q N V g)
    (sourceOriginalPhysicalSourceStepVisits434 q N steps) 0
    (source_original_PHYSICAL_SOURCE_STEP_visits_unit434 q hq hq1 N steps)
    (by simpa only [source_original_PHYSICAL_SOURCE_STEP_visits_sum434,physicalSourceBaseline] using hb)
    (by simpa only [source_original_PHYSICAL_SOURCE_STEP_visits_sum434,physicalSourceBaseline] using hlam)
    mask hm 0 H hH
  simpa only [source_original_PHYSICAL_SOURCE_STEP_visits_sum434,physicalSourceBaseline] using h
end Source

/-- The threshold precedes every moving family, subset B, changing
external seen schedule and joint mask. This is a unit envelope only. -/
theorem eventually_source_original_BACKGROUND_CHAIN_uniform434
    (c : ℝ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {BG : Type} [Fintype BG] [DecidableEq BG]
      (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
      (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
      (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (V : BG → ℝ)
      (hV : ∀ g,0 < V g)
      (hmin : ∀ g p,Real.exp (L^c) ≤ (bm g p:ℝ))
      (g : BG) (hi : Function.Injective (bm g))
      (B : Finset (BP g)) (external : ℕ → Finset ℕ)
      (hext : ∀ i p,p ∈ B → bm g p ∉ external i)
      (steps : ℕ → ℤ)
      (mask : ℕ → Multiset (Atom (BP g) (bm g)) → Finset ℕ →
        Multiset (Atom (BP g) (bm g)) → Finset ℕ → ℂ)
      (hm : ∀ i old seen out st,‖mask i old seen out st‖ ≤ 1)
      (H : Finset ℕ → ℂ) (hH : ∀ st,‖H st‖ ≤ 1),
      ‖(∏ p ∈ B,(physicalSourceBaseline BP bm q (2*Nat.ceil (L^(0.52:ℝ))) g p:ℂ)) *
        sourceOriginalPhysicalNumericBackgroundChain434 (bm g) B external (V g)
          (physicalSourceMuTilde BP bm q (2*Nat.ceil (L^(0.52:ℝ))) V g) mask
          (sourceOriginalPhysicalSourceStepVisits434 q (2*Nat.ceil (L^(0.52:ℝ))) steps) 0
          (fun pending seen => if pending=0 then H seen else 0) 0 (external 0)‖ ≤ 1 := by
  filter_upwards [eventually_source_original_B26_visits_below_BIG434 c hc] with L hL
  intro BG _ _ BP _ _ bm _ q hq hq1 V hV hmin g hi B external hext steps mask hm H hH
  have hb (p : BP g) : 0 < physicalSourceBaseline BP bm q (2*Nat.ceil (L^(0.52:ℝ))) g p := by
    have hh := (source_original_B26_physical_baseline_half434 BP bm q hq hq1
      (2*Nat.ceil (L^(0.52:ℝ))) g p (hL (bm g p) (hmin g p))).1
    linarith only [hh]
  exact source_original_PHYSICAL_SOURCE_BACKGROUND_CHAIN_envelope434 BP bm q hq hq1
    (2*Nat.ceil (L^(0.52:ℝ))) V g (ne_of_gt (hV g)) hi B external hext hb steps mask hm H hH
end Green64Analytic.CorrelationSquare

end

end

