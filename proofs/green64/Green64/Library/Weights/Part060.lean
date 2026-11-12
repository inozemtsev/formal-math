module

public import Green64.Library.Weights.B26NumericMarkedCleanHilbert
public import Green64.Library.Weights.Part056
public import Green64.Library.Weights.Part057
public import Green64.Library.Analysis.Estimates.Part013
public import Green64.Library.Weights.Part027
public import Green64.Library.Correlation.Part048
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Green64.Library.Correlation.PhysicalFramePrimeReturn

@[expose] public section

/-!
# Weights / Part060

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26MarkedEndpointMeanHilbert -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 16000000

variable {G : Type} [Fintype G] [DecidableEq G]
variable (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : G) → BP g → ℕ)
variable (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
local notation "A" => SourceOriginalB26Active434 BP J ell
local notation "Perm" => BigGroupPerm (BG := G) (J+ell)

/-- Both endpoint changes of variables preserve the actual cumulative
inventory, before and after passing to numerical prime values. -/
theorem source_original_B26_MARKED_inventory_permutation434
    (sigma : Perm) (s : A) :
    sourceOriginalBigRefreshPacket434 BP (fun _ => J+ell)
      (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) sigma s) =
    sourceOriginalBigRefreshPacket434 BP (fun _ => J+ell) s := by
  unfold sourceOriginalBigRefreshPacket434
  congr 1
  funext g
  ext p
  constructor
  · intro hp
    obtain ⟨i,hi,hp⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image.mpr ⟨sigma g i,Finset.mem_univ _,hp⟩
  · intro hp
    obtain ⟨i,hi,hp⟩ := Finset.mem_image.mp hp
    apply Finset.mem_image.mpr
    refine ⟨(sigma g).symm i,Finset.mem_univ _,?_⟩
    simpa only [sourceOriginalB26EndpointPermutationEquiv434,Equiv.coe_fn_mk,
      Equiv.apply_symm_apply] using hp

/-- No permutation loss and no density change on numerical histories. -/
theorem source_original_B26_NUMERIC_energy_permutation434
    (sigma : Perm) (mu : (g : G) → BP g → ℝ)
    (f : A → Finset ℕ → ℂ) :
    sourceOriginalB26NumericActiveEnergy434 BP bm J ell mu
      (fun s S => f (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) sigma s) S) =
    sourceOriginalB26NumericActiveEnergy434 BP bm J ell mu f := by
  unfold sourceOriginalB26NumericActiveEnergy434
  apply Finset.sum_congr rfl
  intro S hS
  apply Fintype.sum_equiv (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) sigma)
  intro s
  congr 1
  exact (source_original_B26_endpoint_permutation_mass434 BP (J+ell) mu s sigma).symm

/-- Literal marked CLEAN row with independent source and target endpoint
permutations. Its history records the numerical values of the actual free
target slots. K may be an arbitrary joint function of both endpoints. -/
def sourceOriginalB26NumericPermutedClean434
    (mu : (g : G) → BP g → ℝ) (sigma tau : Perm)
    (K : A → Finset ℕ → A → ℂ) (f : A → Finset ℕ → ℂ)
    (s : A) (S : Finset ℕ) : ℂ :=
  let eS := sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) sigma
  let eT := sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) tau
  if (sourceOriginalBigRefreshPacket434 BP (fun _ => J+ell) s).image
      (fun p : Sigma BP => bm p.1 p.2) ⊆ S then
    ∑ t : A,sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t sigma tau *
      (if Disjoint S ((sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu (eT t)).image
          (fun p : Sigma BP => bm p.1 p.2)) then
        K (eS s) S (eT t) *
          f t (S ∪ (sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu (eT t)).image
            (fun p : Sigma BP => bm p.1 p.2))
       else 0)
  else 0

theorem source_original_B26_NUMERIC_permuted_row434
    (mu : (g : G) → BP g → ℝ) (sigma tau : Perm)
    (K : A → Finset ℕ → A → ℂ) (f : A → Finset ℕ → ℂ) (s : A) (S : Finset ℕ) :
    sourceOriginalB26NumericPermutedClean434 BP bm J ell m hmJ nu mu sigma tau K f s S =
    sourceOriginalB26NumericMarkedClean434 BP bm J ell m hmJ nu mu K
      (fun t T => f ((sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) tau).symm t) T)
      (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) sigma s) S := by
  unfold sourceOriginalB26NumericPermutedClean434 sourceOriginalB26NumericMarkedClean434
  dsimp only
  rw [source_original_B26_MARKED_inventory_permutation434]
  split_ifs with hs
  · apply Fintype.sum_equiv (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) tau)
    intro t
    rw [source_original_B26_fresh_law_permuted434]
    simp only [Equiv.symm_apply_apply]
    rfl
  · rfl

/-- The same marked fresh-slot Hilbert gain for BOTH original endpoint
permutations; all caps of the full joint K are paid, without a factorial loss. -/
theorem source_original_B26_NUMERIC_permuted_Hilbert434
    (hi : Function.Injective (fun p : Sigma BP => bm p.1 p.2))
    (mu : (g : G) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (sigma tau : Perm) (C : ℝ) (hC : 0 ≤ C)
    (K : A → Finset ℕ → A → ℂ) (hK : ∀ s S t,‖K s S t‖ ≤ C)
    (f : A → Finset ℕ → ℂ) :
    sourceOriginalB26NumericActiveEnergy434 BP bm J ell mu
      (sourceOriginalB26NumericPermutedClean434 BP bm J ell m hmJ nu mu sigma tau K f) ≤
    C^2*(∏ g : G,((∑ p : BP g,mu g p)^2/4)^
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g)) *
      sourceOriginalB26NumericActiveEnergy434 BP bm J ell mu f := by
  have he :
      sourceOriginalB26NumericPermutedClean434 BP bm J ell m hmJ nu mu sigma tau K f =
      (fun s S => sourceOriginalB26NumericMarkedClean434 BP bm J ell m hmJ nu mu K
        (fun t T => f ((sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) tau).symm t) T)
        (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) sigma s) S) := by
    funext s S
    exact source_original_B26_NUMERIC_permuted_row434 BP bm J ell m hmJ nu mu sigma tau K f s S
  rw [he,source_original_B26_NUMERIC_energy_permutation434]
  have hh := source_original_B26_NUMERIC_CLEAN_Hilbert434 BP bm J ell m hmJ nu hi
    mu hmu C hC K hK
    (fun t T => f ((sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) tau).symm t) T)
  have hE :
      sourceOriginalB26NumericActiveEnergy434 BP bm J ell mu
        (fun t T => f ((sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) tau).symm t) T) =
      sourceOriginalB26NumericActiveEnergy434 BP bm J ell mu f :=
    source_original_B26_NUMERIC_energy_permutation434 BP bm J ell (fun g => (tau g).symm) mu f
  rwa [hE] at hh

/-- The original total-mass-one double endpoint mean, allowing its true
joint multiplier to depend on the pair of endpoint permutations. -/
def sourceOriginalB26NumericPermutationMean434
    (mu : (g : G) → BP g → ℝ)
    (K : Perm → Perm → A → Finset ℕ → A → ℂ)
    (f : A → Finset ℕ → ℂ) (s : A) (S : Finset ℕ) : ℂ :=
  ∑ st : Perm × Perm,(bigEndpointPairMass (BG := G) (J+ell) : ℂ) *
    sourceOriginalB26NumericPermutedClean434 BP bm J ell m hmJ nu mu st.1 st.2
      (K st.1 st.2) f s S

/-- Genuine double-permutation averaging preserves the fresh-slot bound.
No sum over permutations or histories is charged to the result. -/
theorem source_original_B26_NUMERIC_permutation_mean_Hilbert434
    (hi : Function.Injective (fun p : Sigma BP => bm p.1 p.2))
    (mu : (g : G) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (C : ℝ) (hC : 0 ≤ C)
    (K : Perm → Perm → A → Finset ℕ → A → ℂ)
    (hK : ∀ sigma tau s S t,‖K sigma tau s S t‖ ≤ C)
    (f : A → Finset ℕ → ℂ) :
    sourceOriginalB26NumericActiveEnergy434 BP bm J ell mu
      (sourceOriginalB26NumericPermutationMean434 BP bm J ell m hmJ nu mu K f) ≤
    C^2*(∏ g : G,((∑ p : BP g,mu g p)^2/4)^
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g)) *
      sourceOriginalB26NumericActiveEnergy434 BP bm J ell mu f := by
  let c : ℝ := bigEndpointPairMass (BG := G) (J+ell)
  let R (st : Perm × Perm) :=
    sourceOriginalB26NumericPermutedClean434 BP bm J ell m hmJ nu mu st.1 st.2 (K st.1 st.2) f
  let w (s : A) := sourceOriginalBigRefreshMass434 BP (fun _ => J+ell) mu s
  have hc : 0 ≤ c := source_original_B26_big_permutation_mass_nonneg434 (J+ell)
  have htotal : (∑ st : Perm × Perm,c) = 1 :=
    source_original_B26_big_permutation_mass_total434 (J+ell)
  have hw (s : A) : 0 ≤ w s :=
    Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ => hmu g (s g i)))
  have hp (s : A) (S : Finset ℕ) :
      ‖sourceOriginalB26NumericPermutationMean434 BP bm J ell m hmJ nu mu K f s S‖^2 ≤
      ∑ st : Perm × Perm,c*‖R st s S‖^2 := by
    have hh := source_original_finite_weighted_complex_kernel_CS434
      (fun _ : Perm × Perm => c) (fun _ => hc)
      (fun _ => (1:ℂ)) (fun st => R st s S)
    change ‖∑ st : Perm × Perm,(c:ℂ)*R st s S‖^2 ≤ _
    simpa only [one_mul,norm_one,one_pow,mul_one,htotal] using hh
  calc
    _ ≤ ∑ S ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset,
        ∑ s : A,w s*(∑ st : Perm × Perm,c*‖R st s S‖^2) := by
      apply Finset.sum_le_sum
      intro S hS
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_left (hp s S) (hw s)
    _ = ∑ st : Perm × Perm,c *
        sourceOriginalB26NumericActiveEnergy434 BP bm J ell mu (R st) := by
      simp_rw [Finset.mul_sum]
      trans ∑ S ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset,
        ∑ st : Perm × Perm,∑ s : A,w s*(c*‖R st s S‖^2)
      · apply Finset.sum_congr rfl
        intro S hS
        exact Finset.sum_comm
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro st hst
      unfold sourceOriginalB26NumericActiveEnergy434
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      apply Finset.sum_congr rfl
      intro s hs
      dsimp only [w]
      ring
    _ ≤ ∑ st : Perm × Perm,c *
        (C^2*(∏ g : G,((∑ p : BP g,mu g p)^2/4)^
          (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g)) *
          sourceOriginalB26NumericActiveEnergy434 BP bm J ell mu f) := by
      apply Finset.sum_le_sum
      intro st hst
      exact mul_le_mul_of_nonneg_left
        (source_original_B26_NUMERIC_permuted_Hilbert434 BP bm J ell m hmJ nu hi
          mu hmu st.1 st.2 C hC (K st.1 st.2) (hK st.1 st.2) f) hc
    _ = _ := by rw [← Finset.sum_mul,htotal,one_mul]

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalFiniteJointRows -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Equality of finite weighted marginal rows preserves every JOINT
observation. The output spaces need not be finite. -/
theorem source_original_FINITE_joint_row_congr434
    {I : Type} [Fintype I] [DecidableEq I]
    (A B X : I → Type)
    [∀ i,Fintype (A i)] [∀ i,Fintype (B i)] [∀ i,DecidableEq (X i)]
    (phi : (i : I) → A i → X i) (psi : (i : I) → B i → X i)
    (w : (i : I) → A i → ℂ) (v : (i : I) → B i → ℂ)
    (hrow : ∀ i (f : X i → ℂ),
      (∑ a : A i,w i a * f (phi i a)) = ∑ b : B i,v i b * f (psi i b))
    (F : ((i : I) → X i) → ℂ) :
    (∑ a : (i : I) → A i,(∏ i,w i (a i))*F (fun i => phi i (a i))) =
    ∑ b : (i : I) → B i,(∏ i,v i (b i))*F (fun i => psi i (b i)) := by
  let S : (i : I) → Finset (X i) := fun i =>
    Finset.univ.image (phi i) ∪ Finset.univ.image (psi i)
  let T : I → Type := fun i => {x : X i // x ∈ S i}
  let ph : (i : I) → A i → T i := fun i a => ⟨phi i a,
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ a))⟩
  let ps : (i : I) → B i → T i := fun i b => ⟨psi i b,
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ b))⟩
  have he : ∀ i (t : T i),
      (∑ a : A i,if ph i a=t then w i a else 0) =
      ∑ b : B i,if ps i b=t then v i b else 0 := by
    intro i t
    have h := hrow i (fun x => if x=t.1 then 1 else 0)
    have hph (a : A i) : ph i a=t ↔ phi i a=t.1 := by
      constructor
      · intro hh; exact congrArg Subtype.val hh
      · intro hh; exact Subtype.ext hh
    have hps (b : B i) : ps i b=t ↔ psi i b=t.1 := by
      constructor
      · intro hh; exact congrArg Subtype.val hh
      · intro hh; exact Subtype.ext hh
    simp_rw [hph,hps]
    simpa only [mul_ite,mul_one,mul_zero] using h
  have ha := source_original_FINITE_product_pushforward434 A T ph w
    (fun t => F (fun i => (t i).1))
  have hb := source_original_FINITE_product_pushforward434 B T ps v
    (fun t => F (fun i => (t i).1))
  change (∑ a : (i : I) → A i,(∏ i,w i (a i))*
    (fun t : (i : I) → T i => F (fun i => (t i).1)) (fun i => ph i (a i))) = _
  rw [ha]
  change _ = (∑ b : (i : I) → B i,(∏ i,v i (b i))*
    (fun t : (i : I) → T i => F (fun i => (t i).1)) (fun i => ps i (b i)))
  rw [hb]
  simp_rw [he]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalGhostReturnFullEnvelope -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Once a numerical prime has been born, its absolute keep/delete
weights sum to one. Thus all future pending/retired observations are
controlled without any per-visit multiplier. -/
theorem source_original_GHOST_RETURN_full_terminal_envelope434
    {R : Type} [Fintype R] [DecidableEq R]
    (visits : List (R × ℝ))
    (heta : ∀ v ∈ visits,0 ≤ v.2 ∧ v.2 ≤ 1)
    (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (F : SourceOriginalGhostReturnState434 R → ℂ) (M : ℝ)
    (hf : ∀ s,‖F s‖ ≤ M) :
    ‖sourceOriginalGhostReturnLiteralChain434 visits lambda F .retired‖ ≤ M ∧
    (∀ r,‖sourceOriginalGhostReturnLiteralChain434 visits lambda F (.pending r)‖ ≤ M) ∧
    ‖sourceOriginalGhostReturnLiteralChain434 visits lambda F .unborn‖ ≤
      (1+lambda*(visits.map Prod.snd).sum)*M := by
  have hM : 0 ≤ M := (norm_nonneg (F .unborn)).trans (hf .unborn)
  induction visits with
  | nil => simpa [sourceOriginalGhostReturnLiteralChain434] using
      (show ‖F .retired‖ ≤ M ∧ (∀ r,‖F (.pending r)‖ ≤ M) ∧ ‖F .unborn‖ ≤ M from
        ⟨hf _,fun r => hf _,hf _⟩)
  | cons v vs ih =>
    rcases v with ⟨a,eta⟩
    have hv := heta (a,eta) List.mem_cons_self
    have ht := fun w hw => heta w (List.mem_cons_of_mem (a,eta) hw)
    have hi := ih ht
    have heta0 : 0 ≤ eta := hv.1
    have hq0 : 0 ≤ 1-eta := sub_nonneg.mpr hv.2
    have hec : ‖(eta:ℂ)‖=eta := by simp [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg heta0]
    have hqc : ‖(1-(eta:ℂ))‖=1-eta := by
      calc
        _ = ‖(((1-eta):ℝ):ℂ)‖ := by
          congr 1
          simp only [Complex.ofReal_sub,Complex.ofReal_one]
        _ = 1-eta := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hq0]
    have hlc : ‖(lambda:ℂ)‖=lambda := by
      simp [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlambda]
    refine ⟨?_,?_,?_⟩
    · simpa only [sourceOriginalGhostReturnLiteralChain434,
        source_original_GHOST_RETURN_literal_retired434] using hi.1
    · intro r
      simp only [sourceOriginalGhostReturnLiteralChain434,
        source_original_GHOST_RETURN_literal_pending434]
      split_ifs
      · calc
          _ ≤ ‖(1-(eta:ℂ))*sourceOriginalGhostReturnLiteralChain434 vs lambda F (.pending r)‖+
              ‖(eta:ℂ)*sourceOriginalGhostReturnLiteralChain434 vs lambda F .retired‖ :=
                norm_sub_le _ _
          _ = (1-eta)*‖sourceOriginalGhostReturnLiteralChain434 vs lambda F (.pending r)‖+
              eta*‖sourceOriginalGhostReturnLiteralChain434 vs lambda F .retired‖ := by
                rw [norm_mul,norm_mul,hqc,hec]
          _ ≤ (1-eta)*M+eta*M := add_le_add
                (mul_le_mul_of_nonneg_left (hi.2.1 r) hq0)
                (mul_le_mul_of_nonneg_left hi.1 heta0)
          _ = M := by ring
      · exact hi.2.1 r
    · simp only [sourceOriginalGhostReturnLiteralChain434,
        source_original_GHOST_RETURN_literal_unborn434,List.map_cons,List.sum_cons]
      calc
        _ ≤ ‖sourceOriginalGhostReturnLiteralChain434 vs lambda F .unborn‖+
            ‖(eta:ℂ)*(lambda:ℂ)*sourceOriginalGhostReturnLiteralChain434 vs lambda F (.pending a)‖ :=
              norm_sub_le _ _
        _ = ‖sourceOriginalGhostReturnLiteralChain434 vs lambda F .unborn‖+
            (eta*lambda)*‖sourceOriginalGhostReturnLiteralChain434 vs lambda F (.pending a)‖ := by
              simp only [norm_mul,hec,hlc]
        _ ≤ (1+lambda*(vs.map Prod.snd).sum)*M+(eta*lambda)*M :=
              add_le_add hi.2.2
                (mul_le_mul_of_nonneg_left (hi.2.1 a) (mul_nonneg heta0 hlambda))
        _ = _ := by ring

/-- Exact baseline payment for an arbitrary terminal test on ALL
once-born states, including still-pending ghosts. This is uniform in
the number of visits and retains arbitrary residue return geometry. -/
theorem source_original_GHOST_RETURN_BASELINE_full_envelope434
    {R : Type} [Fintype R] [DecidableEq R] [Nonempty R]
    (visits : List (R × ℝ))
    (heta : ∀ v ∈ visits,0 ≤ v.2 ∧ v.2 ≤ 1)
    (hb : 0 < 1-(visits.map Prod.snd).sum/(Fintype.card R:ℝ))
    (F : SourceOriginalGhostReturnState434 R → ℂ) (M : ℝ)
    (hf : ∀ s,‖F s‖ ≤ M) :
    let p : ℝ := Fintype.card R
    let b := 1-(visits.map Prod.snd).sum/p
    ‖(b:ℂ)*sourceOriginalGhostReturnLiteralChain434 visits (1/(p*b)) F .unborn‖ ≤ M := by
  let p : ℝ := Fintype.card R
  let b := 1-(visits.map Prod.snd).sum/p
  let lam := 1/(p*b)
  have hp : 0 < p := by dsimp [p];exact_mod_cast Fintype.card_pos
  have hb' : 0 < b := hb
  have hl : 0 ≤ lam := by dsimp [lam];positivity
  have hbl : b*lam=1/p := by
    dsimp only [lam]
    field_simp [ne_of_gt hp,ne_of_gt hb']
  have hbalance : b*(1+lam*(visits.map Prod.snd).sum)=1 := by
    calc
      _ = b+(b*lam)*(visits.map Prod.snd).sum := by ring
      _ = b+(1/p)*(visits.map Prod.snd).sum := by rw [hbl]
      _ = 1 := by dsimp [b];ring
  have hi := (source_original_GHOST_RETURN_full_terminal_envelope434 visits heta lam hl F M hf).2.2
  change ‖(b:ℂ)*sourceOriginalGhostReturnLiteralChain434 visits lam F .unborn‖ ≤ M
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hb'.le]
  calc
    _ ≤ b*((1+lam*(visits.map Prod.snd).sum)*M) :=
      mul_le_mul_of_nonneg_left hi hb'.le
    _ = M := by rw [←mul_assoc,hbalance,one_mul]

/-- The preceding full terminal estimate with literal source q_i,
V_g*mu_tilde and baseline. No hGram, hOp, row-bound or fixed-label
analytic premise is added. -/
theorem source_original_PHYSICAL_GHOST_RETURN_full_envelope434
    {BG : Type} [Fintype BG] [DecidableEq BG]
    (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (modulus : (g : BG) → BP g → ℕ) [∀ g p,NeZero (modulus g p)]
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ) (Vb : BG → ℝ)
    (g : BG) (p : BP g) (hV : Vb g ≠ 0)
    (hb : 0 < physicalSourceBaseline BP modulus q N g p)
    (positions : ℕ → ZMod (modulus g p))
    (F : SourceOriginalGhostReturnState434 (ZMod (modulus g p)) → ℂ)
    (M : ℝ) (hf : ∀ s,‖F s‖ ≤ M) :
    ‖(physicalSourceBaseline BP modulus q N g p:ℂ) *
      sourceOriginalGhostReturnLiteralChain434
        (sourceOriginalGhostSourceVisits434 q N positions)
        (Vb g*physicalSourceMuTilde BP modulus q N Vb g p) F .unborn‖ ≤ M := by
  have hp : (modulus g p:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne (modulus g p)
  have hlam : Vb g*physicalSourceMuTilde BP modulus q N Vb g p =
      1/((modulus g p:ℝ)*physicalSourceBaseline BP modulus q N g p) := by
    unfold physicalSourceMuTilde
    field_simp [hV,hp,ne_of_gt hb]
  have hh := source_original_GHOST_RETURN_BASELINE_full_envelope434
    (sourceOriginalGhostSourceVisits434 q N positions)
    (source_original_GHOST_SOURCE_visits_unit434 q hq hq1 N positions)
    (by simpa only [ZMod.card,source_original_GHOST_SOURCE_visits_sum434,
      physicalSourceBaseline] using hb) F M hf
  simpa only [hlam,ZMod.card,source_original_GHOST_SOURCE_visits_sum434,
    physicalSourceBaseline] using hh
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPhysicalGhostBackgroundBirthBudget -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 20000000

theorem source_original_GHOST_RETURN_loops_le_total_eta434
    {R : Type} [Fintype R] [DecidableEq R] (visits : List (R × ℝ))
    (heta : ∀ v ∈ visits,0 ≤ v.2 ∧ v.2 ≤ 1) :
    sourceOriginalGhostReturnLoops434 visits ≤ (visits.map Prod.snd).sum := by
  rw [source_original_GHOST_RETURN_loops_defect434]
  have hh : 0 ≤ ∑ r : R,(1-sourceOriginalGhostReturnSurvival434 visits r) :=
    Finset.sum_nonneg (fun r _ => sub_nonneg.mpr
      (source_original_GHOST_RETURN_survival_unit434 visits heta r).2)
  linarith only [hh]

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (modulus : (g : BG) → BP g → ℕ) [∀ g p,NeZero (modulus g p)]

def sourceOriginalPhysicalGhostBirthMass434
    (q : ℝ) (N : ℕ) (g : BG) (p : BP g)
    (positions : ℕ → ZMod (modulus g p)) : ℝ :=
  sourceOriginalGhostReturnLoops434 (sourceOriginalGhostSourceVisits434 q N positions) /
    (modulus g p:ℝ)

/-- Exact positive history kernel after summing the signed original
birth/death lifespans. The terminal function may be jointly dependent
on every seen label; no factorization of that function is used. -/
theorem source_original_PHYSICAL_GHOST_BACKGROUND_two_history_weights434
    (q : ℝ) (N : ℕ) (Vb : BG → ℝ) (g : BG) (p : BP g)
    (hV : Vb g ≠ 0) (hb : physicalSourceBaseline BP modulus q N g p ≠ 0)
    (positions : ℕ → ZMod (modulus g p)) (seen : Finset ℕ) (F : Finset ℕ → ℂ) :
    sourceOriginalPhysicalGhostBackgroundRow434 BP modulus q N Vb g p positions seen F =
      (physicalSourceBaseline BP modulus q N g p:ℂ)*F seen +
      (sourceOriginalPhysicalGhostBirthMass434 BP modulus q N g p positions:ℂ) *
        (if modulus g p ∈ seen then 0 else F (insert (modulus g p) seen)) := by
  unfold sourceOriginalPhysicalGhostBackgroundRow434
  rw [(source_original_GHOST_RETURN_literal_chain_terminal434 _ _ _ _).2.2]
  have hp : (modulus g p:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne (modulus g p)
  have hlam : physicalSourceBaseline BP modulus q N g p *
      (Vb g*physicalSourceMuTilde BP modulus q N Vb g p) = 1/(modulus g p:ℝ) := by
    unfold physicalSourceMuTilde
    field_simp [hV,hb,hp]
  have hc : ((physicalSourceBaseline BP modulus q N g p:ℂ) *
      ((Vb g*physicalSourceMuTilde BP modulus q N Vb g p:ℝ):ℂ)) =
      ((1/(modulus g p:ℝ):ℝ):ℂ) := by exact_mod_cast hlam
  unfold sourceOriginalPhysicalGhostBirthMass434
  push_cast at hc ⊢
  linear_combination
    (sourceOriginalGhostReturnLoops434 (sourceOriginalGhostSourceVisits434 q N positions):ℂ) *
      (if modulus g p ∈ seen then (0:ℂ) else F (insert (modulus g p) seen)) * hc

theorem source_original_PHYSICAL_GHOST_birth_mass_budget434
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ)
    (g : BG) (p : BP g) (positions : ℕ → ZMod (modulus g p)) :
    0 ≤ sourceOriginalPhysicalGhostBirthMass434 BP modulus q N g p positions ∧
      sourceOriginalPhysicalGhostBirthMass434 BP modulus q N g p positions ≤
        (∑ i ∈ Finset.range (N+1),sourceVisitEta q N i)/(modulus g p:ℝ) := by
  have hp : (0:ℝ) < modulus g p := by exact_mod_cast NeZero.pos (modulus g p)
  have hv := source_original_GHOST_SOURCE_visits_unit434 q hq hq1 N positions
  constructor
  · exact div_nonneg (source_original_GHOST_RETURN_loops_nonneg434 _ hv) hp.le
  · apply (div_le_div_iff_of_pos_right hp).mpr
    simpa only [source_original_GHOST_SOURCE_visits_sum434] using
      source_original_GHOST_RETURN_loops_le_total_eta434 _ hv

def sourceOriginalPhysicalGhostBirthCost434 (q : ℝ) (N : ℕ) (u : ℝ)
    (x : Sigma BP) : ℝ :=
  1+(u-1)*((∑ i ∈ Finset.range (N+1),sourceVisitEta q N i)/(modulus x.1 x.2:ℝ))

theorem source_original_PHYSICAL_GHOST_BACKGROUND_weighted_row434
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ) (Vb : BG → ℝ)
    (g : BG) (p : BP g) (hV : Vb g ≠ 0)
    (hb : 0 < physicalSourceBaseline BP modulus q N g p)
    (positions : ℕ → ZMod (modulus g p))
    (U seen : Finset ℕ) (hpU : modulus g p ∈ U) (hs : seen ⊆ U)
    (F : Finset ℕ → ℂ) (M u : ℝ) (hM : 0 ≤ M) (hu : 1 ≤ u)
    (hf : ∀ t,t ⊆ U → ‖F t‖ ≤ M*u^t.card) :
    ‖sourceOriginalPhysicalGhostBackgroundRow434 BP modulus q N Vb g p positions seen F‖ ≤
      sourceOriginalPhysicalGhostBirthCost434 BP modulus q N u ⟨g,p⟩ * (M*u^seen.card) := by
  let b := physicalSourceBaseline BP modulus q N g p
  let c := sourceOriginalPhysicalGhostBirthMass434 BP modulus q N g p positions
  have hbc := source_original_PHYSICAL_GHOST_birth_mass_budget434 BP modulus q hq hq1 N g p positions
  have hb0 : 0 ≤ b := hb.le
  have hc0 : 0 ≤ c := hbc.1
  have hu0 : 0 ≤ u := zero_le_one.trans hu
  have hpow : 0 ≤ M*u^seen.card := mul_nonneg hM (pow_nonneg hu0 _)
  have hA := hf seen hs
  have hB : ‖if modulus g p ∈ seen then (0:ℂ) else F (insert (modulus g p) seen)‖ ≤
      u*(M*u^seen.card) := by
    by_cases hpSeen : modulus g p ∈ seen
    · rw [if_pos hpSeen,norm_zero]
      exact mul_nonneg hu0 hpow
    · rw [if_neg hpSeen]
      have hh := hf (insert (modulus g p) seen) (Finset.insert_subset_iff.mpr ⟨hpU,hs⟩)
      rw [Finset.card_insert_of_notMem hpSeen,pow_succ] at hh
      nlinarith only [hh]
  have hcost : b+c*u ≤ sourceOriginalPhysicalGhostBirthCost434 BP modulus q N u ⟨g,p⟩ := by
    have hh := mul_le_mul_of_nonneg_right hbc.2 hu0
    dsimp [b,c,sourceOriginalPhysicalGhostBirthCost434,physicalSourceBaseline] at *
    linarith only [hh]
  rw [source_original_PHYSICAL_GHOST_BACKGROUND_two_history_weights434
    BP modulus q N Vb g p hV (ne_of_gt hb)]
  change ‖(b:ℂ)*F seen+(c:ℂ)*(if modulus g p ∈ seen then 0 else F (insert (modulus g p) seen))‖ ≤ _
  calc
    _ ≤ ‖(b:ℂ)*F seen‖+
        ‖(c:ℂ)*(if modulus g p ∈ seen then 0 else F (insert (modulus g p) seen))‖ := norm_add_le _ _
    _ = b*‖F seen‖+
        c*‖if modulus g p ∈ seen then (0:ℂ) else F (insert (modulus g p) seen)‖ := by
          simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hb0,abs_of_nonneg hc0]
    _ ≤ b*(M*u^seen.card)+c*(u*(M*u^seen.card)) :=
          add_le_add (mul_le_mul_of_nonneg_left hA hb0) (mul_le_mul_of_nonneg_left hB hc0)
    _ = (b+c*u)*(M*u^seen.card) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcost hpow

theorem source_original_PHYSICAL_GHOST_BACKGROUND_weighted_chain434
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ) (Vb : BG → ℝ)
    (hV : ∀ g,Vb g ≠ 0)
    (hb : ∀ g p,0 < physicalSourceBaseline BP modulus q N g p)
    (positions : (g : BG) → (p : BP g) → ℕ → ZMod (modulus g p))
    (primes : List (Sigma BP)) (F : Finset ℕ → ℂ) (M u : ℝ)
    (hM : 0 ≤ M) (hu : 1 ≤ u)
    (hf : ∀ t ∈ (sourceOriginalMemoryBirthPool434 BP modulus).powerset,‖F t‖ ≤ M*u^t.card)
    (seen : Finset ℕ) (hs : seen ∈ (sourceOriginalMemoryBirthPool434 BP modulus).powerset) :
    ‖sourceOriginalPhysicalGhostBackgroundChain434 BP modulus q N Vb positions primes F seen‖ ≤
      (primes.map (sourceOriginalPhysicalGhostBirthCost434 BP modulus q N u)).prod *
        (M*u^seen.card) := by
  have hcost (x : Sigma BP) : 0 ≤ sourceOriginalPhysicalGhostBirthCost434 BP modulus q N u x := by
    have hp : (0:ℝ) < modulus x.1 x.2 := by exact_mod_cast NeZero.pos (modulus x.1 x.2)
    have hS := (source_original_B26_visit_sum_unit434 q hq hq1 N).1
    dsimp [sourceOriginalPhysicalGhostBirthCost434]
    exact add_nonneg zero_le_one (mul_nonneg (sub_nonneg.mpr hu) (div_nonneg hS hp.le))
  induction primes generalizing seen with
  | nil => simpa [sourceOriginalPhysicalGhostBackgroundChain434] using hf seen hs
  | cons x xs ih =>
    have hprod : 0 ≤ (xs.map (sourceOriginalPhysicalGhostBirthCost434 BP modulus q N u)).prod :=
      List.prod_nonneg (fun a ha => by
        obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ha
        exact hcost z)
    have hh := source_original_PHYSICAL_GHOST_BACKGROUND_weighted_row434
      BP modulus q hq hq1 N Vb x.1 x.2 (hV x.1) (hb x.1 x.2) (positions x.1 x.2)
      (sourceOriginalMemoryBirthPool434 BP modulus) seen
      (Finset.mem_biUnion.mpr ⟨x.1,Finset.mem_univ _,Finset.mem_image.mpr ⟨x.2,Finset.mem_univ _,rfl⟩⟩)
      (Finset.mem_powerset.mp hs)
      (sourceOriginalPhysicalGhostBackgroundChain434 BP modulus q N Vb positions xs F)
      ((xs.map (sourceOriginalPhysicalGhostBirthCost434 BP modulus q N u)).prod*M) u
      (mul_nonneg hprod hM) hu
      (fun t ht => by
        have hh := ih t (Finset.mem_powerset.mpr ht)
        simpa only [mul_assoc] using hh)
    simpa only [sourceOriginalPhysicalGhostBackgroundChain434,List.map_cons,List.prod_cons,
      mul_assoc] using hh
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPhysicalGhostBackgroundBirthTail -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 20000000

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (modulus : (g : BG) → BP g → ℕ) [∀ g p,NeZero (modulus g p)]

/-- The exact generating-function cost depends on the original
harmonic mass, not the cardinality of the background alphabet. -/
theorem source_original_PHYSICAL_GHOST_birth_cost_exponential434
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ) (u : ℝ) (hu : 1 ≤ u)
    (primes : List (Sigma BP)) :
    (primes.map (sourceOriginalPhysicalGhostBirthCost434 BP modulus q N u)).prod ≤
      Real.exp ((u-1)*(∑ i ∈ Finset.range (N+1),sourceVisitEta q N i) *
        (primes.map (fun x => 1/(modulus x.1 x.2:ℝ))).sum) := by
  let S := ∑ i ∈ Finset.range (N+1),sourceVisitEta q N i
  have hS : 0 ≤ S := (source_original_B26_visit_sum_unit434 q hq hq1 N).1
  have hcost (x : Sigma BP) : 0 ≤ sourceOriginalPhysicalGhostBirthCost434 BP modulus q N u x := by
    have hp : (0:ℝ) < modulus x.1 x.2 := by exact_mod_cast NeZero.pos (modulus x.1 x.2)
    exact add_nonneg zero_le_one (mul_nonneg (sub_nonneg.mpr hu) (div_nonneg hS hp.le))
  induction primes with
  | nil => simp
  | cons x xs ih =>
    have hx : sourceOriginalPhysicalGhostBirthCost434 BP modulus q N u x ≤
        Real.exp ((u-1)*S/(modulus x.1 x.2:ℝ)) := by
      simpa only [sourceOriginalPhysicalGhostBirthCost434,mul_div_assoc,add_comm] using
        Real.add_one_le_exp ((u-1)*S/(modulus x.1 x.2:ℝ))
    have hp : 0 ≤ (xs.map (sourceOriginalPhysicalGhostBirthCost434 BP modulus q N u)).prod :=
      List.prod_nonneg (fun a ha => by
        obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ha
        exact hcost z)
    simp only [List.map_cons,List.prod_cons,List.sum_cons]
    calc
      _ ≤ Real.exp ((u-1)*S/(modulus x.1 x.2:ℝ)) *
          Real.exp ((u-1)*S*(xs.map (fun x => 1/(modulus x.1 x.2:ℝ))).sum) :=
            mul_le_mul hx ih hp (Real.exp_pos _).le
      _ = _ := by
        rw [←Real.exp_add]
        congr 1
        dsimp only [S]
        ring

/-- Tail of NEW global birth values in the resummed background chain.
Both the initial seen set and the terminal test are arbitrary; the
test may couple all history labels. This is not yet the OLD tail of
the full mixed source E/G chain. -/
theorem source_original_PHYSICAL_GHOST_BACKGROUND_birth_tail434
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ) (Vb : BG → ℝ)
    (hV : ∀ g,Vb g ≠ 0)
    (hb : ∀ g p,0 < physicalSourceBaseline BP modulus q N g p)
    (positions : (g : BG) → (p : BP g) → ℕ → ZMod (modulus g p))
    (primes : List (Sigma BP)) (F : Finset ℕ → ℂ)
    (hf : ∀ t ∈ (sourceOriginalMemoryBirthPool434 BP modulus).powerset,‖F t‖ ≤ 1)
    (seen : Finset ℕ) (hs : seen ∈ (sourceOriginalMemoryBirthPool434 BP modulus).powerset)
    (H : ℕ) (u : ℝ) (hu : 1 ≤ u) :
    ‖sourceOriginalPhysicalGhostBackgroundChain434 BP modulus q N Vb positions primes
      (fun t => if H+seen.card ≤ t.card then F t else 0) seen‖ ≤
      Real.exp ((u-1)*(∑ i ∈ Finset.range (N+1),sourceVisitEta q N i) *
        (primes.map (fun x => 1/(modulus x.1 x.2:ℝ))).sum) / u^H := by
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hMf : ∀ t ∈ (sourceOriginalMemoryBirthPool434 BP modulus).powerset,
      ‖if H+seen.card ≤ t.card then F t else (0:ℂ)‖ ≤
        (1/u^(H+seen.card))*u^t.card := by
    intro t ht
    by_cases htail : H+seen.card ≤ t.card
    · rw [if_pos htail]
      have hh := pow_le_pow_right₀ hu htail
      calc
        _ ≤ 1 := hf t ht
        _ ≤ (1/u^(H+seen.card))*u^t.card := by
          rw [one_div_mul_eq_div]
          exact (one_le_div (pow_pos hu0 _)).mpr hh
    · rw [if_neg htail,norm_zero]
      positivity
  have hh := source_original_PHYSICAL_GHOST_BACKGROUND_weighted_chain434
    BP modulus q hq hq1 N Vb hV hb positions primes
    (fun t => if H+seen.card ≤ t.card then F t else 0)
    (1/u^(H+seen.card)) u (by positivity) hu hMf seen hs
  have he : (1/u^(H+seen.card))*u^seen.card=1/u^H := by
    rw [pow_add]
    field_simp [ne_of_gt hu0]
  rw [he] at hh
  have hc := source_original_PHYSICAL_GHOST_birth_cost_exponential434 BP modulus q hq hq1 N u hu primes
  calc
    _ ≤ (primes.map (sourceOriginalPhysicalGhostBirthCost434 BP modulus q N u)).prod * (1/u^H) := hh
    _ ≤ _ := by
      rw [mul_one_div]
      exact (div_le_div_iff_of_pos_right (pow_pos hu0 _)).mpr hc
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPhysicalGhostBackgroundSourceBoxTail -/

section

open Filter
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- The source uses distinct NUMERICAL primes. A crude full-integer
harmonic bound already controls their total mass without counting
groups or labels; no additional prime theorem is required. -/
theorem source_original_GHOST_numeric_harmonic_box434
    {I : Type} [DecidableEq I] (m : I → ℕ) (s : Finset I)
    (hinj : Function.Injective m) (hpos : ∀ x ∈ s,0 < m x)
    (X : ℝ) (hX : 1 ≤ X) (hmax : ∀ x ∈ s,(m x:ℝ) ≤ X) :
    (s.toList.map (fun x => 1/(m x:ℝ))).sum ≤ 1+Real.log X := by
  rw [Finset.sum_map_toList]
  have hsub : s.image m ⊆ Finset.Icc 1 (Nat.floor X) := by
    intro n hn
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_Icc.mpr ⟨hpos x hx,Nat.le_floor (hmax x hx)⟩
  calc
    _ = ∑ n ∈ s.image m,1/(n:ℝ) := by
      symm
      exact Finset.sum_image (fun x hx y hy hh => hinj hh)
    _ ≤ ∑ n ∈ Finset.Icc 1 (Nat.floor X),1/(n:ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn hnot => by positivity)
    _ = (harmonic (Nat.floor X):ℝ) := by
      simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div]
    _ ≤ _ := harmonic_floor_le_one_add_log X hX

/-- Applicable source-depth birth-tail bound with the TRUE moving
alphabet's explicit box and global numerical injectivity. The eventual
threshold is before all family/history/test data. The maximum alphabet
mass costs 1+sqrt(L), not its cardinality, even without Mertens. -/
theorem eventually_source_original_PHYSICAL_GHOST_BACKGROUND_source_box_tail434
    (c : ℝ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {BG : Type} [Fintype BG] [DecidableEq BG]
      (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
      (modulus : (g : BG) → BP g → ℕ) [∀ g p,NeZero (modulus g p)]
      (hinj : Function.Injective (fun x : Sigma BP => modulus x.1 x.2))
      (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (Vb : BG → ℝ)
      (hV : ∀ g,0 < Vb g)
      (hmin : ∀ g p,Real.exp (L^c) ≤ (modulus g p:ℝ))
      (hmax : ∀ g p,(modulus g p:ℝ) ≤ Real.exp (Real.sqrt L))
      (positions : (g : BG) → (p : BP g) → ℕ → ZMod (modulus g p))
      (primes : Finset (Sigma BP)) (F : Finset ℕ → ℂ)
      (hf : ∀ t ∈ (sourceOriginalMemoryBirthPool434 BP modulus).powerset,‖F t‖ ≤ 1)
      (seen : Finset ℕ) (hs : seen ∈ (sourceOriginalMemoryBirthPool434 BP modulus).powerset)
      (H : ℕ) (u : ℝ) (hu : 1 ≤ u),
      ‖sourceOriginalPhysicalGhostBackgroundChain434 BP modulus q
        (2*Nat.ceil (L^(0.52:ℝ))) Vb positions primes.toList
        (fun t => if H+seen.card ≤ t.card then F t else 0) seen‖ ≤
      Real.exp ((u-1)*((2*Nat.ceil (L^(0.52:ℝ))+1:ℕ):ℝ)*(1+Real.sqrt L))/u^H := by
  filter_upwards [eventually_source_original_B26_visits_below_BIG434 c hc] with L hL
  intro BG _ _ BP _ _ modulus _ hinj q hq hq1 Vb hV hmin hmax positions primes F hf seen hs H u hu
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  have hb (g : BG) (p : BP g) : 0 < physicalSourceBaseline BP modulus q N g p := by
    have hh := (source_original_B26_physical_baseline_half434 BP modulus q hq hq1 N g p
      (hL (modulus g p) (hmin g p))).1
    linarith only [hh]
  have hsigma : (primes.toList.map (fun x => 1/(modulus x.1 x.2:ℝ))).sum ≤ 1+Real.sqrt L := by
    have hh := source_original_GHOST_numeric_harmonic_box434
      (fun x : Sigma BP => modulus x.1 x.2) primes hinj
      (fun x _ => NeZero.pos _) (Real.exp (Real.sqrt L))
      (Real.one_le_exp_iff.mpr (Real.sqrt_nonneg L)) (fun x _ => hmax x.1 x.2)
    simpa only [Real.log_exp] using hh
  have hS := source_original_B26_visit_sum_unit434 q hq hq1 N
  have ht := source_original_PHYSICAL_GHOST_BACKGROUND_birth_tail434 BP modulus q hq hq1 N
    Vb (fun g => ne_of_gt (hV g)) hb positions primes.toList F hf seen hs H u hu
  apply ht.trans
  apply (div_le_div_iff_of_pos_right (pow_pos (zero_lt_one.trans_le hu) H)).mpr
  apply Real.exp_le_exp.mpr
  have hu0 := sub_nonneg.mpr hu
  calc
    _ ≤ (u-1)*(∑ i ∈ Finset.range (N+1),sourceVisitEta q N i)*(1+Real.sqrt L) :=
      mul_le_mul_of_nonneg_left hsigma (mul_nonneg hu0 hS.1)
    _ ≤ (u-1)*((N+1:ℕ):ℝ)*(1+Real.sqrt L) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS.2 hu0)
        (by positivity)

/-- Concrete generating parameter and source OLD scale. This bounds
new background births >=ceil(L²); no full mixed-chain OLD-tail claim
or logarithmic saving is hidden in the statement. -/
theorem eventually_source_original_PHYSICAL_GHOST_BACKGROUND_L2_birth_cut434
    (c : ℝ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {BG : Type} [Fintype BG] [DecidableEq BG]
      (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
      (modulus : (g : BG) → BP g → ℕ) [∀ g p,NeZero (modulus g p)]
      (hinj : Function.Injective (fun x : Sigma BP => modulus x.1 x.2))
      (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (Vb : BG → ℝ)
      (hV : ∀ g,0 < Vb g)
      (hmin : ∀ g p,Real.exp (L^c) ≤ (modulus g p:ℝ))
      (hmax : ∀ g p,(modulus g p:ℝ) ≤ Real.exp (Real.sqrt L))
      (positions : (g : BG) → (p : BP g) → ℕ → ZMod (modulus g p))
      (primes : Finset (Sigma BP)) (F : Finset ℕ → ℂ)
      (hf : ∀ t ∈ (sourceOriginalMemoryBirthPool434 BP modulus).powerset,‖F t‖ ≤ 1)
      (seen : Finset ℕ) (hs : seen ∈ (sourceOriginalMemoryBirthPool434 BP modulus).powerset),
      ‖sourceOriginalPhysicalGhostBackgroundChain434 BP modulus q
        (2*Nat.ceil (L^(0.52:ℝ))) Vb positions primes.toList
        (fun t => if Nat.ceil (L^2)+seen.card ≤ t.card then F t else 0) seen‖ ≤
      Real.exp (((2*Nat.ceil (L^(0.52:ℝ))+1:ℕ):ℝ)*(1+Real.sqrt L))/(2:ℝ)^Nat.ceil (L^2) := by
  filter_upwards [eventually_source_original_PHYSICAL_GHOST_BACKGROUND_source_box_tail434 c hc] with L hL
  intro BG _ _ BP _ _ modulus _ hinj q hq hq1 Vb hV hmin hmax positions primes F hf seen hs
  have hh := hL BP modulus hinj q hq hq1 Vb hV hmin hmax positions primes F hf seen hs
    (Nat.ceil (L^2)) 2 (by norm_num)
  simpa only [show (2:ℝ)-1=1 by norm_num,one_mul] using hh
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalGhostReturnMaskedVacuum -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {R : Type} [Fintype R] [DecidableEq R]

/-- The entrywise absolute coefficients of the once-born row, valid
for 0 <= eta <= 1 and lambda >= 0. This is not an extra assumed norm. -/
def sourceOriginalGhostReturnPositiveRow434
    (a : R) (eta lambda : ℝ) (F : SourceOriginalGhostReturnState434 R → ℝ) :
    SourceOriginalGhostReturnState434 R → ℝ
  | .unborn => F .unborn + eta*lambda*F (.pending a)
  | .pending r => if r=a then (1-eta)*F (.pending r)+eta*F .retired else F (.pending r)
  | .retired => F .retired

def sourceOriginalGhostReturnPositiveChain434
    (visits : List (R × ℝ)) (lambda : ℝ)
    (F : SourceOriginalGhostReturnState434 R → ℝ) :
    SourceOriginalGhostReturnState434 R → ℝ :=
  match visits with
  | [] => F
  | v::vs => sourceOriginalGhostReturnPositiveRow434 v.1 v.2 lambda
      (sourceOriginalGhostReturnPositiveChain434 vs lambda F)

/-- In a completed once-born vacuum path, birth and deletion are both
present or both absent. Their two signs pair; the positive vacuum
chain has the same unborn value as the original signed chain. -/
theorem source_original_GHOST_RETURN_positive_vacuum434
    (visits : List (R × ℝ)) (lambda : ℝ) :
    sourceOriginalGhostReturnPositiveChain434 visits lambda
        sourceOriginalGhostReturnVacuum434 .retired = 1 ∧
    (∀ r,sourceOriginalGhostReturnPositiveChain434 visits lambda
        sourceOriginalGhostReturnVacuum434 (.pending r) =
      1-sourceOriginalGhostReturnSurvival434 visits r) ∧
    sourceOriginalGhostReturnPositiveChain434 visits lambda
        sourceOriginalGhostReturnVacuum434 .unborn =
      1+lambda*sourceOriginalGhostReturnLoops434 visits := by
  induction visits with
  | nil => simp [sourceOriginalGhostReturnPositiveChain434,
      sourceOriginalGhostReturnVacuum434,sourceOriginalGhostReturnSurvival434,
      sourceOriginalGhostReturnLoops434]
  | cons v vs ih =>
      rcases v with ⟨a,eta⟩
      refine ⟨?_,?_,?_⟩
      · exact ih.1
      · intro r
        simp only [sourceOriginalGhostReturnPositiveChain434,sourceOriginalGhostReturnPositiveRow434,
          sourceOriginalGhostReturnSurvival434]
        rw [ih.1,ih.2.1 r]
        split_ifs <;> ring
      · simp only [sourceOriginalGhostReturnPositiveChain434,sourceOriginalGhostReturnPositiveRow434,
          sourceOriginalGhostReturnLoops434]
        rw [ih.2.2,ih.2.1 a]
        ring

theorem source_original_GHOST_RETURN_row_norm_majorant434
    (a : R) (eta lambda : ℝ) (heta : 0 ≤ eta) (heta1 : eta ≤ 1) (hlambda : 0 ≤ lambda)
    (F : SourceOriginalGhostReturnState434 R → ℂ)
    (G : SourceOriginalGhostReturnState434 R → ℝ)
    (hFG : ∀ s,‖F s‖ ≤ G s) (s : SourceOriginalGhostReturnState434 R) :
    ‖sourceOriginalGhostReturnLiteralRow434 a eta lambda s F‖ ≤
      sourceOriginalGhostReturnPositiveRow434 a eta lambda G s := by
  have he : ‖(eta:ℂ)‖=eta := by simp [Real.norm_eq_abs,abs_of_nonneg heta]
  have hl : ‖(lambda:ℂ)‖=lambda := by simp [Real.norm_eq_abs,abs_of_nonneg hlambda]
  have hc : ‖(1:ℂ)-(eta:ℂ)‖=1-eta := by
    rw [show (1:ℂ)-(eta:ℂ)=((1-eta:ℝ):ℂ) by simp]
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr heta1)]
  cases s with
  | unborn =>
      rw [source_original_GHOST_RETURN_literal_unborn434]
      change ‖_‖ ≤ G .unborn+eta*lambda*G (.pending a)
      calc
        _ ≤ ‖F .unborn‖+‖(eta:ℂ)*(lambda:ℂ)*F (.pending a)‖ := norm_sub_le _ _
        _ = ‖F .unborn‖+eta*lambda*‖F (.pending a)‖ := by rw [norm_mul,norm_mul,he,hl]
        _ ≤ _ := add_le_add (hFG _) (mul_le_mul_of_nonneg_left (hFG _) (mul_nonneg heta hlambda))
  | retired =>
      rw [source_original_GHOST_RETURN_literal_retired434]
      exact hFG _
  | pending r =>
      rw [source_original_GHOST_RETURN_literal_pending434]
      by_cases hr : r=a
      · rw [if_pos hr]
        change ‖_‖ ≤ if r=a then (1-eta)*G (.pending r)+eta*G .retired else G (.pending r)
        rw [if_pos hr]
        calc
          _ ≤ ‖((1:ℂ)-(eta:ℂ))*F (.pending r)‖+‖(eta:ℂ)*F .retired‖ := norm_sub_le _ _
          _ = (1-eta)*‖F (.pending r)‖+eta*‖F .retired‖ := by rw [norm_mul,norm_mul,hc,he]
          _ ≤ _ := add_le_add
            (mul_le_mul_of_nonneg_left (hFG _) (sub_nonneg.mpr heta1))
            (mul_le_mul_of_nonneg_left (hFG _) heta)
      · simpa only [if_neg hr,sourceOriginalGhostReturnPositiveRow434] using hFG (.pending r)

/-- Arbitrary complex masks of BOTH adjacent return states at EVERY
visit. In particular, time-dependent projection masks may be inserted
without factorizing them into functions of the two endpoint states. -/
def sourceOriginalGhostReturnMaskedChain434
    (visits : List (R × ℝ)) (lambda : ℝ)
    (mask : ℕ → SourceOriginalGhostReturnState434 R → SourceOriginalGhostReturnState434 R → ℂ)
    (start : ℕ) (F : SourceOriginalGhostReturnState434 R → ℂ) :
    SourceOriginalGhostReturnState434 R → ℂ :=
  match visits with
  | [] => F
  | v::vs => fun s => sourceOriginalGhostReturnLiteralRow434 v.1 v.2 lambda s
      (fun t => mask start s t * sourceOriginalGhostReturnMaskedChain434 vs lambda mask (start+1) F t)

theorem source_original_GHOST_RETURN_masked_chain_majorant434
    (visits : List (R × ℝ)) (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (heta : ∀ v ∈ visits,0 ≤ v.2 ∧ v.2 ≤ 1)
    (mask : ℕ → SourceOriginalGhostReturnState434 R → SourceOriginalGhostReturnState434 R → ℂ)
    (hmask : ∀ i s t,‖mask i s t‖ ≤ 1)
    (F : SourceOriginalGhostReturnState434 R → ℂ)
    (G : SourceOriginalGhostReturnState434 R → ℝ)
    (hFG : ∀ s,‖F s‖ ≤ G s) (start : ℕ) (s : SourceOriginalGhostReturnState434 R) :
    ‖sourceOriginalGhostReturnMaskedChain434 visits lambda mask start F s‖ ≤
      sourceOriginalGhostReturnPositiveChain434 visits lambda G s := by
  induction visits generalizing start s with
  | nil => exact hFG s
  | cons v vs ih =>
      have hv := heta v List.mem_cons_self
      have ht := fun w hw => heta w (List.mem_cons_of_mem v hw)
      apply source_original_GHOST_RETURN_row_norm_majorant434
        v.1 v.2 lambda hv.1 hv.2 hlambda
      intro t
      calc
        _ = ‖mask start s t‖ *
          ‖sourceOriginalGhostReturnMaskedChain434 vs lambda mask (start+1) F t‖ := norm_mul _ _
        _ ≤ 1*‖sourceOriginalGhostReturnMaskedChain434 vs lambda mask (start+1) F t‖ :=
          mul_le_mul_of_nonneg_right (hmask start s t) (norm_nonneg _)
        _ ≤ _ := by simpa only [one_mul] using ih ht (start+1) t

/-- No per-visit loss: arbitrary contractive complex masks preserve the
baseline bound on the complete once-born marked vacuum pairing. Both
terminal seen histories are retained. This is restricted to a single
never-active prime; no assertion about the full mixed root is made. -/
theorem source_original_GHOST_RETURN_MASKED_baseline_envelope434
    [Nonempty R] (visits : List (R × ℝ))
    (heta : ∀ v ∈ visits,0 ≤ v.2 ∧ v.2 ≤ 1)
    (hb : 0 < 1-(visits.map Prod.snd).sum/(Fintype.card R:ℝ))
    (mask : ℕ → SourceOriginalGhostReturnState434 R → SourceOriginalGhostReturnState434 R → ℂ)
    (hmask : ∀ i s t,‖mask i s t‖ ≤ 1)
    (start : ℕ) (A B : ℂ) (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    let p : ℝ := Fintype.card R
    let b := 1-(visits.map Prod.snd).sum/p
    ‖(b:ℂ)*sourceOriginalGhostReturnMaskedChain434 visits (1/(p*b)) mask start
      (sourceOriginalGhostReturnTerminal434 A B) .unborn‖ ≤ 1 := by
  let p : ℝ := Fintype.card R
  let b := 1-(visits.map Prod.snd).sum/p
  let lambda := 1/(p*b)
  have hp : 0 < p := by dsimp [p];exact_mod_cast Fintype.card_pos
  have hb' : 0 < b := hb
  have hl : 0 ≤ lambda := by dsimp [lambda];positivity
  have hf (s : SourceOriginalGhostReturnState434 R) :
      ‖sourceOriginalGhostReturnTerminal434 A B s‖ ≤ sourceOriginalGhostReturnVacuum434 s := by
    cases s with
    | unborn => exact hA
    | retired => exact hB
    | pending _ => simp [sourceOriginalGhostReturnTerminal434,sourceOriginalGhostReturnVacuum434]
  have hn := source_original_GHOST_RETURN_masked_chain_majorant434 visits lambda hl heta
    mask hmask (sourceOriginalGhostReturnTerminal434 A B) sourceOriginalGhostReturnVacuum434 hf start .unborn
  rw [(source_original_GHOST_RETURN_positive_vacuum434 visits lambda).2.2] at hn
  have hu := (source_original_GHOST_RETURN_BASELINE_unit434 visits heta (ne_of_gt hb)).2
  rw [(source_original_GHOST_RETURN_chain_exact434 visits _).2.2] at hu
  change ‖(b:ℂ)*sourceOriginalGhostReturnMaskedChain434 visits lambda mask start
    (sourceOriginalGhostReturnTerminal434 A B) .unborn‖ ≤ 1
  calc
    _ = b*‖sourceOriginalGhostReturnMaskedChain434 visits lambda mask start
        (sourceOriginalGhostReturnTerminal434 A B) .unborn‖ := by
      rw [norm_mul]
      simp [Real.norm_eq_abs,abs_of_nonneg hb'.le]
    _ ≤ b*(1+lambda*sourceOriginalGhostReturnLoops434 visits) :=
      mul_le_mul_of_nonneg_left hn hb'.le
    _ ≤ 1 := hu
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPhysicalPrimePoolMajorant -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 18000000

section Positive
variable {R : Type} [Fintype R] [DecidableEq R]
def sourceOriginalGhostReturnPositiveKernel434
    (a : R) (eta lambda : ℝ) (s t : SourceOriginalGhostReturnState434 R) : ℝ :=
  sourceOriginalGhostReturnPositiveRow434 a eta lambda (fun u => if u=t then 1 else 0) s

theorem source_original_RETURN_positive_kernel_sum434
    (a : R) (eta lambda : ℝ) (s : SourceOriginalGhostReturnState434 R)
    (G : SourceOriginalGhostReturnState434 R → ℝ) :
    (∑ t,sourceOriginalGhostReturnPositiveKernel434 a eta lambda s t * G t) =
      sourceOriginalGhostReturnPositiveRow434 a eta lambda G s := by
  cases s with
  | unborn => simp [sourceOriginalGhostReturnPositiveKernel434,
      sourceOriginalGhostReturnPositiveRow434,add_mul,Finset.sum_add_distrib,
      mul_ite,ite_mul,← Finset.mul_sum]
  | retired => simp [sourceOriginalGhostReturnPositiveKernel434,
      sourceOriginalGhostReturnPositiveRow434,ite_mul]
  | pending r =>
      by_cases h : r=a <;> simp [sourceOriginalGhostReturnPositiveKernel434,
        sourceOriginalGhostReturnPositiveRow434,h,add_mul,Finset.sum_add_distrib,
        mul_ite,ite_mul,← Finset.mul_sum]

theorem source_original_RETURN_positive_row_nonneg434
    (a : R) (eta lambda : ℝ) (he : 0 ≤ eta) (he1 : eta ≤ 1) (hl : 0 ≤ lambda)
    (G : SourceOriginalGhostReturnState434 R → ℝ) (hG : ∀ s,0 ≤ G s)
    (s : SourceOriginalGhostReturnState434 R) :
    0 ≤ sourceOriginalGhostReturnPositiveRow434 a eta lambda G s := by
  cases s with
  | unborn => exact add_nonneg (hG _) (mul_nonneg (mul_nonneg he hl) (hG _))
  | retired => exact hG _
  | pending r =>
      change 0 ≤ if r=a then (1-eta)*G (.pending r)+eta*G .retired else G (.pending r)
      split_ifs
      · exact add_nonneg (mul_nonneg (sub_nonneg.mpr he1) (hG _)) (mul_nonneg he (hG _))
      · exact hG _

theorem source_original_RETURN_positive_chain_nonneg434
    (vs : List (R × ℝ)) (lambda : ℝ) (hl : 0 ≤ lambda)
    (he : ∀ v ∈ vs,0 ≤ v.2 ∧ v.2 ≤ 1)
    (G : SourceOriginalGhostReturnState434 R → ℝ) (hG : ∀ s,0 ≤ G s)
    (s : SourceOriginalGhostReturnState434 R) :
    0 ≤ sourceOriginalGhostReturnPositiveChain434 vs lambda G s := by
  induction vs generalizing s with
  | nil => exact hG s
  | cons v vs ih =>
      exact source_original_RETURN_positive_row_nonneg434 v.1 v.2 lambda
        (he v List.mem_cons_self).1 (he v List.mem_cons_self).2 hl _
        (fun t => ih (fun w hw => he w (List.mem_cons_of_mem v hw)) t) s

theorem source_original_RETURN_kernel_norm434
    (a : R) (eta lambda : ℝ) (he : 0 ≤ eta) (he1 : eta ≤ 1) (hl : 0 ≤ lambda)
    (s t : SourceOriginalGhostReturnState434 R) :
    ‖sourceOriginalGhostReturnLiteralRow434 a eta lambda s (fun u => if u=t then 1 else 0)‖ ≤
      sourceOriginalGhostReturnPositiveKernel434 a eta lambda s t := by
  apply source_original_GHOST_RETURN_row_norm_majorant434 a eta lambda he he1 hl
  intro u
  by_cases h : u=t <;> simp [h]
end Positive

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]

/-- Product majorant for the actual signed return matrix. The complex
test remains joint; only its nonnegative envelope is a product. -/
theorem source_original_PRIME_PRODUCT_return_row_majorant434
    (shift : ℤ) (s : SourceOriginalPrimeReturnProductState434 modulus)
    (eta V : ℝ) (mu : P → ℝ)
    (he : 0 ≤ eta) (he1 : eta ≤ 1) (hl : ∀ p,0 ≤ V*mu p)
    (F : SourceOriginalPrimeReturnProductState434 modulus → ℂ)
    (G : (p : P) → SourceOriginalGhostReturnState434 (ZMod (modulus p)) → ℝ)
    (hG : ∀ p t,0 ≤ G p t) (hFG : ∀ t,‖F t‖ ≤ ∏ p,G p (t p)) :
    ‖sourceOriginalPrimeProductReturnRow434 modulus shift s eta V mu F‖ ≤
      ∏ p,sourceOriginalGhostReturnPositiveRow434 (-(shift : ZMod (modulus p)))
        eta (V*mu p) (G p) (s p) := by
  let K := fun p t => sourceOriginalGhostReturnPositiveKernel434
    (-(shift : ZMod (modulus p))) eta (V*mu p) (s p) t
  have hK (p : P) (t : SourceOriginalGhostReturnState434 (ZMod (modulus p))) :
      ‖sourceOriginalPrimeReturnKernel434 modulus p shift eta V mu (s p) t‖ ≤ K p t :=
    source_original_RETURN_kernel_norm434 _ eta (V*mu p) he he1 (hl p) (s p) t
  have hK0 (p : P) (t : SourceOriginalGhostReturnState434 (ZMod (modulus p))) :
      0 ≤ K p t := le_trans (norm_nonneg _) (hK p t)
  unfold sourceOriginalPrimeProductReturnRow434
  calc
    _ ≤ ∑ t,‖(∏ p,sourceOriginalPrimeReturnKernel434 modulus p shift eta V mu (s p) (t p))*F t‖ :=
      norm_sum_le _ _
    _ = ∑ t,(∏ p,‖sourceOriginalPrimeReturnKernel434 modulus p shift eta V mu (s p) (t p)‖)*‖F t‖ := by
      simp only [norm_mul,norm_prod]
    _ ≤ ∑ t : SourceOriginalPrimeReturnProductState434 modulus,(∏ p,K p (t p))*(∏ p,G p (t p)) := by
      apply Finset.sum_le_sum
      intro t ht
      exact mul_le_mul
        (Finset.prod_le_prod₀ (fun p hp => norm_nonneg _) (fun p hp => hK p (t p)))
        (hFG t) (norm_nonneg _) (Finset.prod_nonneg (fun p hp => hK0 p (t p)))
    _ = ∏ p,∑ t,K p t * G p t := by
      simp only [← Finset.prod_mul_distrib,Fintype.prod_sum]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      exact source_original_RETURN_positive_kernel_sum434 _ _ _ _ _

/-- Exact coordinate vacuum envelope for an arbitrary joint observation
of the complete seen set. No factorization of that observation is used. -/
theorem source_original_PRIME_PRODUCT_joint_vacuum_majorant434
    (shift : ℤ) (s : SourceOriginalPrimeReturnProductState434 modulus)
    (H : Finset P → ℂ) (hH : ∀ st,‖H st‖ ≤ 1) :
    ‖if sourceOriginalPrimeProductPending434 modulus shift s=0 then
        H (sourceOriginalPrimeProductSeen434 modulus s) else 0‖ ≤
      ∏ p,sourceOriginalGhostReturnVacuum434 (s p) := by
  by_cases h : sourceOriginalPrimeProductPending434 modulus shift s=0
  · rw [if_pos h]
    have hp (p : P) : sourceOriginalOnePrimePending434 modulus p shift (s p)=0 := by
      rw [← source_original_PRIME_PRODUCT_pending_filter434 modulus shift s p,h]
      simp
    have hv (p : P) : sourceOriginalGhostReturnVacuum434 (s p)=1 := by
      cases hs : s p with
      | unborn => rfl
      | retired => rfl
      | pending r =>
          have hh := congrArg Multiset.card (hp p)
          simp [hs,sourceOriginalOnePrimePending434] at hh
    simpa only [hv,Finset.prod_const_one] using hH (sourceOriginalPrimeProductSeen434 modulus s)
  · rw [if_neg h,norm_zero]
    apply Finset.prod_nonneg
    intro p hp
    cases s p <;> simp [sourceOriginalGhostReturnVacuum434]

/-- A literal simultaneous physical pool, over all visits, with arbitrary
joint contractive masks and arbitrary bounded joint terminal seen test.
No cardinality, visit-count, conductor or fine-cell factor is incurred. -/
theorem source_original_PHYSICAL_PRIME_POOL_masked_vacuum_majorant434
    (V : ℝ) (mu : P → ℝ) (hl : ∀ p,0 ≤ V*mu p)
    (mask : ℕ → Multiset (Atom P modulus) → Finset P →
      Multiset (Atom P modulus) → Finset P → ℂ)
    (hm : ∀ i old seen out st,‖mask i old seen out st‖ ≤ 1)
    (vs : List (ℝ × ℤ)) (he : ∀ v ∈ vs,0 ≤ v.1 ∧ v.1 ≤ 1)
    (H : Finset P → ℂ) (hH : ∀ st,‖H st‖ ≤ 1)
    (shift : ℤ) (start : ℕ) (s : SourceOriginalPrimeReturnProductState434 modulus) :
    ‖sourceOriginalPhysicalPrimePoolMaskedChain434 modulus V mu mask vs start
      (fun pending seen => if pending=0 then H seen else 0)
      (sourceOriginalPrimeProductPending434 modulus shift s)
      (sourceOriginalPrimeProductSeen434 modulus s)‖ ≤
    ∏ p,sourceOriginalGhostReturnPositiveChain434
      (sourceOriginalSinglePrimeVisits434 modulus p shift vs) (V*mu p)
      sourceOriginalGhostReturnVacuum434 (s p) := by
  induction vs generalizing shift start s with
  | nil => exact source_original_PRIME_PRODUCT_joint_vacuum_majorant434 modulus shift s H hH
  | cons v vs ih =>
      have hv := he v List.mem_cons_self
      have ht := fun w hw => he w (List.mem_cons_of_mem v hw)
      dsimp only [sourceOriginalPhysicalPrimePoolMaskedChain434,
        sourceOriginalSinglePrimeVisits434,sourceOriginalGhostReturnPositiveChain434]
      rw [source_original_PRIME_POOL_G_return_matrix434]
      apply source_original_PRIME_PRODUCT_return_row_majorant434 modulus shift s v.1 V mu
        hv.1 hv.2 hl
      · intro p t
        apply source_original_RETURN_positive_chain_nonneg434 _ (V*mu p) (hl p)
        · intro w hw
          exact source_original_PHYSICAL_SINGLE_PRIME_visits_unit434 modulus p vs ht (shift+v.2) w hw
        · intro u
          cases u <;> simp [sourceOriginalGhostReturnVacuum434]
      · intro t
        rw [norm_mul]
        apply le_trans (mul_le_mul_of_nonneg_right (hm _ _ _ _ _) (norm_nonneg _))
        rw [one_mul,source_original_PRIME_PRODUCT_translate434]
        exact ih ht (shift+v.2) (start+1) t
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPhysicalSinglePrimeMasked -/

section

open Filter
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]
variable (p : P)

abbrev SourceOriginalSinglePrimePhysicalMask434 :=
  ℕ → Multiset (Atom P modulus) → Bool → Multiset (Atom P modulus) → Bool → ℂ

/-- Original singleton G rows and integer translations, with an
arbitrary joint mask on the physical input and translated output.
Neither the mask nor the terminal seen observation is factorized. -/
def sourceOriginalPhysicalSinglePrimeMaskedChain434 (V : ℝ) (mu : P → ℝ) :
    List (ℝ × ℤ) → SourceOriginalSinglePrimePhysicalMask434 modulus → ℕ →
    (Multiset (Atom P modulus) → Bool → ℂ) →
    Multiset (Atom P modulus) → Bool → ℂ
  | [],_,_,F => F
  | v::vs,mask,start,F => fun pending seen =>
      sourceOriginalPhysicalSinglePrimeG434 modulus p v.1 V mu pending seen
        (fun out s =>
          mask start pending seen (out.map (translateAtom v.2)) s *
          sourceOriginalPhysicalSinglePrimeMaskedChain434 V mu vs mask (start+1) F
            (out.map (translateAtom v.2)) s)

theorem source_original_PHYSICAL_SINGLE_PRIME_MASKED_majorant434
    (V : ℝ) (mu : P → ℝ) (hlambda : 0 ≤ V*mu p)
    (vs : List (ℝ × ℤ)) (heta : ∀ v ∈ vs,0 ≤ v.1 ∧ v.1 ≤ 1)
    (shift : ℤ) (mask : SourceOriginalSinglePrimePhysicalMask434 modulus)
    (hmask : ∀ i old seen out seen',‖mask i old seen out seen'‖ ≤ 1)
    (start : ℕ) (H : Bool → ℂ) (hH : ∀ s,‖H s‖ ≤ 1)
    (s : SourceOriginalGhostReturnState434 (ZMod (modulus p))) :
    ‖sourceOriginalPhysicalSinglePrimeMaskedChain434 modulus p V mu vs mask start
      (sourceOriginalSinglePrimeVacuumObservation434 modulus H)
      (sourceOriginalOnePrimePending434 modulus p shift s) (sourceOriginalOnePrimeSeen434 s)‖ ≤
      sourceOriginalGhostReturnPositiveChain434 (sourceOriginalSinglePrimeVisits434 modulus p shift vs)
        (V*mu p) sourceOriginalGhostReturnVacuum434 s := by
  induction vs generalizing shift start s with
  | nil =>
      change ‖sourceOriginalSinglePrimeVacuumObservation434 modulus H
        (sourceOriginalOnePrimePending434 modulus p shift s) (sourceOriginalOnePrimeSeen434 s)‖ ≤
        sourceOriginalGhostReturnVacuum434 s
      rw [source_original_PHYSICAL_SINGLE_PRIME_vacuum_terminal434]
      cases s with
      | unborn => exact hH false
      | retired => exact hH true
      | pending _ => simp [sourceOriginalGhostReturnTerminal434,sourceOriginalGhostReturnVacuum434]
  | cons v vs ih =>
      have hv := heta v List.mem_cons_self
      have ht := fun w hw => heta w (List.mem_cons_of_mem v hw)
      dsimp only [sourceOriginalPhysicalSinglePrimeMaskedChain434,
        sourceOriginalSinglePrimeVisits434,sourceOriginalGhostReturnPositiveChain434]
      rw [source_original_PHYSICAL_SINGLE_PRIME_G_pullback434,
        source_original_PHYSICAL_SINGLE_PRIME_return_row434]
      apply source_original_GHOST_RETURN_row_norm_majorant434
        (-(shift : ZMod (modulus p))) v.1 (V*mu p) hv.1 hv.2 hlambda
      intro t
      calc
        _ = ‖mask start (sourceOriginalOnePrimePending434 modulus p shift s)
            (sourceOriginalOnePrimeSeen434 s)
            ((sourceOriginalOnePrimePending434 modulus p shift t).map (translateAtom v.2))
            (sourceOriginalOnePrimeSeen434 t)‖ *
            ‖sourceOriginalPhysicalSinglePrimeMaskedChain434 modulus p V mu vs mask (start+1)
              (sourceOriginalSinglePrimeVacuumObservation434 modulus H)
              ((sourceOriginalOnePrimePending434 modulus p shift t).map (translateAtom v.2))
              (sourceOriginalOnePrimeSeen434 t)‖ := norm_mul _ _
        _ ≤ 1*‖sourceOriginalPhysicalSinglePrimeMaskedChain434 modulus p V mu vs mask (start+1)
              (sourceOriginalSinglePrimeVacuumObservation434 modulus H)
              ((sourceOriginalOnePrimePending434 modulus p shift t).map (translateAtom v.2))
              (sourceOriginalOnePrimeSeen434 t)‖ :=
          mul_le_mul_of_nonneg_right (hmask _ _ _ _ _) (norm_nonneg _)
        _ = ‖sourceOriginalPhysicalSinglePrimeMaskedChain434 modulus p V mu vs mask (start+1)
              (sourceOriginalSinglePrimeVacuumObservation434 modulus H)
              (sourceOriginalOnePrimePending434 modulus p (shift+v.2) t)
              (sourceOriginalOnePrimeSeen434 t)‖ := by
          rw [one_mul,source_original_PHYSICAL_SINGLE_PRIME_translate434]
        _ ≤ _ := ih ht (shift+v.2) (start+1) t

/-- A genuine masked physical vacuum bound. The baseline pays for the
whole once-born return chain, with no factor per time or per mask. -/
theorem source_original_PHYSICAL_SINGLE_PRIME_MASKED_baseline434
    (V : ℝ) (mu : P → ℝ) (vs : List (ℝ × ℤ)) (shift : ℤ)
    (heta : ∀ v ∈ vs,0 ≤ v.1 ∧ v.1 ≤ 1)
    (hb : 0 < 1-(vs.map Prod.fst).sum/(modulus p:ℝ))
    (hlam : V*mu p = 1/((modulus p:ℝ)*(1-(vs.map Prod.fst).sum/(modulus p:ℝ))))
    (mask : SourceOriginalSinglePrimePhysicalMask434 modulus)
    (hmask : ∀ i old seen out seen',‖mask i old seen out seen'‖ ≤ 1)
    (start : ℕ) (H : Bool → ℂ) (hH : ∀ s,‖H s‖ ≤ 1) :
    ‖((1-(vs.map Prod.fst).sum/(modulus p:ℝ):ℝ):ℂ) *
      sourceOriginalPhysicalSinglePrimeMaskedChain434 modulus p V mu vs mask start
        (sourceOriginalSinglePrimeVacuumObservation434 modulus H) 0 false‖ ≤ 1 := by
  let b : ℝ := 1-(vs.map Prod.fst).sum/(modulus p:ℝ)
  have hb' : 0 < b := hb
  have hp : (0:ℝ) < modulus p := by exact_mod_cast NeZero.pos (modulus p)
  have hl : 0 ≤ V*mu p := by rw [hlam];positivity
  have hn := source_original_PHYSICAL_SINGLE_PRIME_MASKED_majorant434 modulus p V mu hl
    vs heta shift mask hmask start H hH .unborn
  simp only [sourceOriginalOnePrimePending434,sourceOriginalOnePrimeSeen434] at hn
  rw [(source_original_GHOST_RETURN_positive_vacuum434
    (sourceOriginalSinglePrimeVisits434 modulus p shift vs) (V*mu p)).2.2] at hn
  have hu := (source_original_GHOST_RETURN_BASELINE_unit434
    (sourceOriginalSinglePrimeVisits434 modulus p shift vs)
    (source_original_PHYSICAL_SINGLE_PRIME_visits_unit434 modulus p vs heta shift)
    (by simpa only [ZMod.card,source_original_PHYSICAL_SINGLE_PRIME_visits_sum434]
      using ne_of_gt hb)).2
  rw [(source_original_GHOST_RETURN_chain_exact434
    (sourceOriginalSinglePrimeVisits434 modulus p shift vs) _).2.2] at hu
  simp only [ZMod.card,source_original_PHYSICAL_SINGLE_PRIME_visits_sum434] at hu
  rw [←hlam] at hu
  change ‖(b:ℂ)*sourceOriginalPhysicalSinglePrimeMaskedChain434 modulus p V mu vs mask start
    (sourceOriginalSinglePrimeVacuumObservation434 modulus H) 0 false‖ ≤ 1
  calc
    _ = b*‖sourceOriginalPhysicalSinglePrimeMaskedChain434 modulus p V mu vs mask start
        (sourceOriginalSinglePrimeVacuumObservation434 modulus H) 0 false‖ := by
      rw [norm_mul]
      simp [Real.norm_eq_abs,abs_of_nonneg hb'.le]
    _ ≤ b*(1+(V*mu p)*sourceOriginalGhostReturnLoops434
        (sourceOriginalSinglePrimeVisits434 modulus p shift vs)) :=
      mul_le_mul_of_nonneg_left hn hb'.le
    _ ≤ 1 := hu

section Source

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]

theorem source_original_PHYSICAL_SOURCE_SINGLE_PRIME_MASKED_envelope434
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ) (V : BG → ℝ)
    (g : BG) (p : BP g) (hV : V g ≠ 0)
    (hb : 0 < physicalSourceBaseline BP bm q N g p)
    (steps : ℕ → ℤ) (mask : SourceOriginalSinglePrimePhysicalMask434 (bm g))
    (hmask : ∀ i old seen out seen',‖mask i old seen out seen'‖ ≤ 1)
    (H : Bool → ℂ) (hH : ∀ s,‖H s‖ ≤ 1) :
    ‖(physicalSourceBaseline BP bm q N g p:ℂ) *
      sourceOriginalPhysicalSinglePrimeMaskedChain434 (bm g) p (V g)
        (physicalSourceMuTilde BP bm q N V g)
        (sourceOriginalPhysicalSourceStepVisits434 q N steps) mask 0
        (sourceOriginalSinglePrimeVacuumObservation434 (bm g) H) 0 false‖ ≤ 1 := by
  have hp : (bm g p:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne (bm g p)
  have hlam : V g*physicalSourceMuTilde BP bm q N V g p =
      1/((bm g p:ℝ)*physicalSourceBaseline BP bm q N g p) := by
    unfold physicalSourceMuTilde
    field_simp [hV,hp,ne_of_gt hb]
  have ht := source_original_PHYSICAL_SINGLE_PRIME_MASKED_baseline434
    (bm g) p (V g) (physicalSourceMuTilde BP bm q N V g)
    (sourceOriginalPhysicalSourceStepVisits434 q N steps) 0
    (source_original_PHYSICAL_SOURCE_STEP_visits_unit434 q hq hq1 N steps)
    (by simpa only [source_original_PHYSICAL_SOURCE_STEP_visits_sum434,
      physicalSourceBaseline] using hb)
    (by simpa only [source_original_PHYSICAL_SOURCE_STEP_visits_sum434,
      physicalSourceBaseline] using hlam) mask hmask 0 H hH
  simpa only [source_original_PHYSICAL_SOURCE_STEP_visits_sum434,physicalSourceBaseline] using ht

end Source

/-- Uniformity in the ORIGINAL moving source-depth data, including
all joint physical masks. Baseline positivity is derived from the
physical BIG-prime lower scale after a single c-dependent threshold. -/
theorem eventually_source_original_PHYSICAL_SINGLE_PRIME_MASKED_uniform434
    (c : ℝ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {BG : Type} [Fintype BG] [DecidableEq BG]
      (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
      (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
      (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (V : BG → ℝ)
      (hV : ∀ g,0 < V g)
      (hmin : ∀ g p,Real.exp (L^c) ≤ (bm g p:ℝ))
      (g : BG) (p : BP g) (steps : ℕ → ℤ)
      (mask : SourceOriginalSinglePrimePhysicalMask434 (bm g))
      (hmask : ∀ i old seen out seen',‖mask i old seen out seen'‖ ≤ 1)
      (H : Bool → ℂ) (hH : ∀ s,‖H s‖ ≤ 1),
      ‖(physicalSourceBaseline BP bm q (2*Nat.ceil (L^(0.52:ℝ))) g p:ℂ) *
        sourceOriginalPhysicalSinglePrimeMaskedChain434 (bm g) p (V g)
          (physicalSourceMuTilde BP bm q (2*Nat.ceil (L^(0.52:ℝ))) V g)
          (sourceOriginalPhysicalSourceStepVisits434 q (2*Nat.ceil (L^(0.52:ℝ))) steps) mask 0
          (sourceOriginalSinglePrimeVacuumObservation434 (bm g) H) 0 false‖ ≤ 1 := by
  filter_upwards [eventually_source_original_B26_visits_below_BIG434 c hc] with L hL
  intro BG _ _ BP _ _ bm _ q hq hq1 V hV hmin g p steps mask hmask H hH
  have hb : 0 < physicalSourceBaseline BP bm q (2*Nat.ceil (L^(0.52:ℝ))) g p := by
    have hh := (source_original_B26_physical_baseline_half434 BP bm q hq hq1
      (2*Nat.ceil (L^(0.52:ℝ))) g p (hL (bm g p) (hmin g p))).1
    linarith only [hh]
  exact source_original_PHYSICAL_SOURCE_SINGLE_PRIME_MASKED_envelope434 BP bm q hq hq1
    (2*Nat.ceil (L^(0.52:ℝ))) V g p (ne_of_gt (hV g)) hb steps mask hmask H hH
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPhysicalPrimePoolBaseline -/

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

/-- One baseline per genuine prime pays for the entire literal
simultaneous pool chain, including arbitrary joint masks and the
complete terminal seen observable. There is no size or depth bound. -/
theorem source_original_PHYSICAL_PRIME_POOL_MASKED_baseline434
    (V : ℝ) (mu : P → ℝ) (vs : List (ℝ × ℤ)) (shift : ℤ)
    (he : ∀ v ∈ vs,0 ≤ v.1 ∧ v.1 ≤ 1)
    (hb : ∀ p,0 < 1-(vs.map Prod.fst).sum/(modulus p:ℝ))
    (hlam : ∀ p,V*mu p = 1/((modulus p:ℝ)*(1-(vs.map Prod.fst).sum/(modulus p:ℝ))))
    (mask : ℕ → Multiset (Atom P modulus) → Finset P →
      Multiset (Atom P modulus) → Finset P → ℂ)
    (hm : ∀ i old seen out st,‖mask i old seen out st‖ ≤ 1)
    (start : ℕ) (H : Finset P → ℂ) (hH : ∀ st,‖H st‖ ≤ 1) :
    ‖(∏ p,((1-(vs.map Prod.fst).sum/(modulus p:ℝ):ℝ):ℂ)) *
      sourceOriginalPhysicalPrimePoolMaskedChain434 modulus V mu mask vs start
        (fun pending seen => if pending=0 then H seen else 0) 0 ∅‖ ≤ 1 := by
  let b : P → ℝ := fun p => 1-(vs.map Prod.fst).sum/(modulus p:ℝ)
  let A : P → ℝ := fun p => sourceOriginalGhostReturnPositiveChain434
    (sourceOriginalSinglePrimeVisits434 modulus p shift vs) (V*mu p)
    sourceOriginalGhostReturnVacuum434 .unborn
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
  have hn := source_original_PHYSICAL_PRIME_POOL_masked_vacuum_majorant434
    modulus V mu hl mask hm vs he H hH shift start (fun _ => .unborn)
  simp only [sourceOriginalPrimeProductPending434,sourceOriginalOnePrimePending434,
    Finset.sum_const_zero,sourceOriginalPrimeProductSeen434,
    sourceOriginalOnePrimeSeen434,Bool.false_eq_true,Finset.filter_false] at hn
  have hu (p : P) : b p*A p ≤ 1 := by
    have h := (source_original_GHOST_RETURN_BASELINE_unit434
      (sourceOriginalSinglePrimeVisits434 modulus p shift vs)
      (source_original_PHYSICAL_SINGLE_PRIME_visits_unit434 modulus p vs he shift)
      (by simpa only [ZMod.card,source_original_PHYSICAL_SINGLE_PRIME_visits_sum434]
        using ne_of_gt (hb p))).2
    rw [(source_original_GHOST_RETURN_chain_exact434
      (sourceOriginalSinglePrimeVisits434 modulus p shift vs) _).2.2] at h
    simp only [ZMod.card,source_original_PHYSICAL_SINGLE_PRIME_visits_sum434] at h
    rw [←hlam p] at h
    dsimp only [b,A]
    rw [(source_original_GHOST_RETURN_positive_vacuum434
      (sourceOriginalSinglePrimeVisits434 modulus p shift vs) (V*mu p)).2.2]
    exact h
  change ‖(∏ p,(b p:ℂ)) * _‖ ≤ 1
  calc
    _ = (∏ p,b p) * ‖sourceOriginalPhysicalPrimePoolMaskedChain434 modulus V mu mask vs start
        (fun pending seen => if pending=0 then H seen else 0) 0 ∅‖ := by
      rw [norm_mul,norm_prod]
      congr 1
      apply Finset.prod_congr rfl
      intro p hp
      simp only [Complex.norm_real,Real.norm_eq_abs]
      exact abs_of_nonneg (show 0 ≤ b p from (hb p).le)
    _ ≤ (∏ p,b p)*(∏ p,A p) :=
      mul_le_mul_of_nonneg_left hn (Finset.prod_nonneg (fun p hp => (hb p).le))
    _ = ∏ p,b p*A p := (Finset.prod_mul_distrib).symm
    _ ≤ ∏ p,(1:ℝ) := Finset.prod_le_prod₀
      (fun p hp => mul_nonneg (hb p).le (hA p)) (fun p hp => hu p)
    _ = 1 := by simp

section Source
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]

theorem source_original_PHYSICAL_SOURCE_PRIME_POOL_MASKED_envelope434
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ) (V : BG → ℝ)
    (g : BG) (hV : V g ≠ 0)
    (hb : ∀ p,0 < physicalSourceBaseline BP bm q N g p)
    (steps : ℕ → ℤ)
    (mask : ℕ → Multiset (Atom (BP g) (bm g)) → Finset (BP g) →
      Multiset (Atom (BP g) (bm g)) → Finset (BP g) → ℂ)
    (hm : ∀ i old seen out st,‖mask i old seen out st‖ ≤ 1)
    (H : Finset (BP g) → ℂ) (hH : ∀ st,‖H st‖ ≤ 1) :
    ‖(∏ p,(physicalSourceBaseline BP bm q N g p:ℂ)) *
      sourceOriginalPhysicalPrimePoolMaskedChain434 (bm g) (V g)
        (physicalSourceMuTilde BP bm q N V g) mask
        (sourceOriginalPhysicalSourceStepVisits434 q N steps) 0
        (fun pending seen => if pending=0 then H seen else 0) 0 ∅‖ ≤ 1 := by
  have hlam (p : BP g) : V g*physicalSourceMuTilde BP bm q N V g p =
      1/((bm g p:ℝ)*physicalSourceBaseline BP bm q N g p) := by
    have hp : (bm g p:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne (bm g p)
    unfold physicalSourceMuTilde
    field_simp [hV,hp,ne_of_gt (hb p)]
  have h := source_original_PHYSICAL_PRIME_POOL_MASKED_baseline434
    (bm g) (V g) (physicalSourceMuTilde BP bm q N V g)
    (sourceOriginalPhysicalSourceStepVisits434 q N steps) 0
    (source_original_PHYSICAL_SOURCE_STEP_visits_unit434 q hq hq1 N steps)
    (by simpa only [source_original_PHYSICAL_SOURCE_STEP_visits_sum434,physicalSourceBaseline] using hb)
    (by simpa only [source_original_PHYSICAL_SOURCE_STEP_visits_sum434,physicalSourceBaseline] using hlam)
    mask hm 0 H hH
  simpa only [source_original_PHYSICAL_SOURCE_STEP_visits_sum434,physicalSourceBaseline] using h
end Source

/-- A single threshold depending only on c precedes every moving finite
group and prime family, all visits, all joint physical masks, and all
joint terminal seen tests. This is a unit envelope, not log saving. -/
theorem eventually_source_original_PHYSICAL_PRIME_POOL_MASKED_uniform434
    (c : ℝ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {BG : Type} [Fintype BG] [DecidableEq BG]
      (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
      (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
      (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (V : BG → ℝ)
      (hV : ∀ g,0 < V g)
      (hmin : ∀ g p,Real.exp (L^c) ≤ (bm g p:ℝ))
      (g : BG) (steps : ℕ → ℤ)
      (mask : ℕ → Multiset (Atom (BP g) (bm g)) → Finset (BP g) →
        Multiset (Atom (BP g) (bm g)) → Finset (BP g) → ℂ)
      (hm : ∀ i old seen out st,‖mask i old seen out st‖ ≤ 1)
      (H : Finset (BP g) → ℂ) (hH : ∀ st,‖H st‖ ≤ 1),
      ‖(∏ p,(physicalSourceBaseline BP bm q (2*Nat.ceil (L^(0.52:ℝ))) g p:ℂ)) *
        sourceOriginalPhysicalPrimePoolMaskedChain434 (bm g) (V g)
          (physicalSourceMuTilde BP bm q (2*Nat.ceil (L^(0.52:ℝ))) V g) mask
          (sourceOriginalPhysicalSourceStepVisits434 q (2*Nat.ceil (L^(0.52:ℝ))) steps) 0
          (fun pending seen => if pending=0 then H seen else 0) 0 ∅‖ ≤ 1 := by
  filter_upwards [eventually_source_original_B26_visits_below_BIG434 c hc] with L hL
  intro BG _ _ BP _ _ bm _ q hq hq1 V hV hmin g steps mask hm H hH
  have hb (p : BP g) : 0 < physicalSourceBaseline BP bm q (2*Nat.ceil (L^(0.52:ℝ))) g p := by
    have hh := (source_original_B26_physical_baseline_half434 BP bm q hq hq1
      (2*Nat.ceil (L^(0.52:ℝ))) g p (hL (bm g p) (hmin g p))).1
    linarith only [hh]
  exact source_original_PHYSICAL_SOURCE_PRIME_POOL_MASKED_envelope434 BP bm q hq hq1
    (2*Nat.ceil (L^(0.52:ℝ))) V g (ne_of_gt (hV g)) hb steps mask hm H hH
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPhysicalPrimePoolNumericChain -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]

/-- Literal physical pool G with the original numerical no-rebirth
gate and numerical seen update, on arbitrary pending and seen input. -/
def sourceOriginalPhysicalNumericPrimePoolG434
    (eta V : ℝ) (mu : P → ℝ) (pending : Multiset (Atom P modulus))
    (seen : Finset ℕ) (F : Multiset (Atom P modulus) → Finset ℕ → ℂ) : ℂ :=
  ∑ d : SourceOriginalRestrictedPrimeBirthChoice434 modulus
      (pending.toFinset.filter (fun z => z.2=0)) Finset.univ,
    if ∀ p ∈ d.2.1,modulus p ∉ seen then
      sourceOriginalGroupPrimeBirthWeight434 modulus
        (pending.toFinset.filter (fun z => z.2=0))
        (-(eta:ℂ)) (1-(eta:ℂ)) (-(eta:ℂ)*(V:ℂ)) (fun p => (mu p:ℂ))
        (sourceOriginalRestrictedPrimeBirthLift434 modulus _ _ d) *
      F (sourceOriginalGhostPiecePending434 modulus pending.toFinset d.1.1 d.2.1)
        (seen ∪ d.2.1.image modulus)
    else 0

theorem source_original_NUMERIC_PRIME_POOL_G_return_matrix434
    (shift : ℤ) (s : SourceOriginalPrimeReturnProductState434 modulus)
    (hi : Function.Injective modulus) (external : Finset ℕ)
    (hext : ∀ p,modulus p ∉ external)
    (eta V : ℝ) (mu : P → ℝ)
    (F : Multiset (Atom P modulus) → Finset ℕ → ℂ) :
    sourceOriginalPhysicalNumericPrimePoolG434 modulus eta V mu
      (sourceOriginalPrimeProductPending434 modulus shift s)
      (external ∪ (sourceOriginalPrimeProductSeen434 modulus s).image modulus) F =
    sourceOriginalPrimeProductReturnRow434 modulus shift s eta V mu
      (fun t => F (sourceOriginalPrimeProductPending434 modulus shift t)
        (external ∪ (sourceOriginalPrimeProductSeen434 modulus t).image modulus)) :=
  source_original_PRIME_PRODUCT_numeric_G_return_matrix434
    modulus shift s hi external hext eta V mu F

def sourceOriginalPhysicalNumericPrimePoolMaskedChain434
    (V : ℝ) (mu : P → ℝ)
    (mask : ℕ → Multiset (Atom P modulus) → Finset ℕ →
      Multiset (Atom P modulus) → Finset ℕ → ℂ) :
    List (ℝ × ℤ) → ℕ → (Multiset (Atom P modulus) → Finset ℕ → ℂ) →
      Multiset (Atom P modulus) → Finset ℕ → ℂ
  | [],_,F => F
  | v::vs,start,F => fun pending seen =>
      sourceOriginalPhysicalNumericPrimePoolG434 modulus v.1 V mu pending seen
        (fun out st =>
          mask start pending seen (out.map (translateAtom v.2)) st *
          sourceOriginalPhysicalNumericPrimePoolMaskedChain434 V mu mask vs (start+1) F
            (out.map (translateAtom v.2)) st)

/-- Temporal numerical seen transport for the actual pool chain.
The external numerical seen set is retained inside every joint mask
and terminal observation, and every actual no-rebirth gate is kept. -/
theorem source_original_NUMERIC_PRIME_POOL_masked_chain_pullback434
    (hi : Function.Injective modulus) (external : Finset ℕ)
    (hext : ∀ p,modulus p ∉ external)
    (V : ℝ) (mu : P → ℝ)
    (mask : ℕ → Multiset (Atom P modulus) → Finset ℕ →
      Multiset (Atom P modulus) → Finset ℕ → ℂ)
    (vs : List (ℝ × ℤ)) (shift : ℤ) (start : ℕ)
    (F : Multiset (Atom P modulus) → Finset ℕ → ℂ)
    (s : SourceOriginalPrimeReturnProductState434 modulus) :
    sourceOriginalPhysicalNumericPrimePoolMaskedChain434 modulus V mu mask vs start F
      (sourceOriginalPrimeProductPending434 modulus shift s)
      (external ∪ (sourceOriginalPrimeProductSeen434 modulus s).image modulus) =
    sourceOriginalPhysicalPrimePoolMaskedChain434 modulus V mu
      (fun i old seen out st => mask i old (external ∪ seen.image modulus)
        out (external ∪ st.image modulus)) vs start
      (fun pending seen => F pending (external ∪ seen.image modulus))
      (sourceOriginalPrimeProductPending434 modulus shift s)
      (sourceOriginalPrimeProductSeen434 modulus s) := by
  induction vs generalizing shift start s with
  | nil => rfl
  | cons v vs ih =>
      dsimp only [sourceOriginalPhysicalNumericPrimePoolMaskedChain434,
        sourceOriginalPhysicalPrimePoolMaskedChain434]
      rw [source_original_NUMERIC_PRIME_POOL_G_return_matrix434 modulus shift s hi external hext,
        source_original_PRIME_POOL_G_return_matrix434]
      unfold sourceOriginalPrimeProductReturnRow434
      apply Finset.sum_congr rfl
      intro t ht
      dsimp only
      simp only [source_original_PRIME_PRODUCT_translate434]
      rw [ih (shift+v.2) (start+1) t]

/-- Genuine full-numerical-seen unit envelope for a pure physical pool.
External seen labels are fixed and disjoint from the pool; no claim
about extraction through the full mixed E/G root is made here. -/
theorem source_original_NUMERIC_PRIME_POOL_MASKED_baseline434
    (hi : Function.Injective modulus) (external : Finset ℕ)
    (hext : ∀ p,modulus p ∉ external)
    (V : ℝ) (mu : P → ℝ) (vs : List (ℝ × ℤ)) (shift : ℤ)
    (he : ∀ v ∈ vs,0 ≤ v.1 ∧ v.1 ≤ 1)
    (hb : ∀ p,0 < 1-(vs.map Prod.fst).sum/(modulus p:ℝ))
    (hlam : ∀ p,V*mu p = 1/((modulus p:ℝ)*(1-(vs.map Prod.fst).sum/(modulus p:ℝ))))
    (mask : ℕ → Multiset (Atom P modulus) → Finset ℕ →
      Multiset (Atom P modulus) → Finset ℕ → ℂ)
    (hm : ∀ i old seen out st,‖mask i old seen out st‖ ≤ 1)
    (start : ℕ) (H : Finset ℕ → ℂ) (hH : ∀ st,‖H st‖ ≤ 1) :
    ‖(∏ p,((1-(vs.map Prod.fst).sum/(modulus p:ℝ):ℝ):ℂ)) *
      sourceOriginalPhysicalNumericPrimePoolMaskedChain434 modulus V mu mask vs start
        (fun pending seen => if pending=0 then H seen else 0) 0 external‖ ≤ 1 := by
  have ht := source_original_NUMERIC_PRIME_POOL_masked_chain_pullback434 modulus
    hi external hext V mu mask vs shift start
    (fun pending seen => if pending=0 then H seen else 0) (fun _ => .unborn)
  simp only [sourceOriginalPrimeProductPending434,sourceOriginalOnePrimePending434,
    Finset.sum_const_zero,sourceOriginalPrimeProductSeen434,
    sourceOriginalOnePrimeSeen434,Bool.false_eq_true,Finset.filter_false,
    Finset.image_empty,Finset.union_empty] at ht
  rw [ht]
  apply source_original_PHYSICAL_PRIME_POOL_MASKED_baseline434 modulus V mu vs shift he hb hlam
  · intro i old seen out st
    exact hm i old (external ∪ seen.image modulus) out (external ∪ st.image modulus)
  · intro st
    exact hH (external ∪ st.image modulus)
end Green64Analytic.CorrelationSquare

end

end

