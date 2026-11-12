module

public import Green64.Library.Analysis.Estimates.AllPrimeAnchors
public import Green64.Library.Analysis.Estimates.AllPrimeArray

@[expose] public section

/-!
# Analysis / Estimates / AllPrimeDamping

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## AllPrimeDamping -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option maxRecDepth 12000
set_option linter.unusedSectionVars false

section Family
variable {G : Type} [Fintype G] [DecidableEq G]
variable (P : G → Type) [∀ g, Fintype (P g)] [∀ g, DecidableEq (P g)]
variable (mod : (g : G) → P g → ℕ) [∀ g p, NeZero (mod g p)]

theorem b643_mark_visit_mem434 (M N : ℕ)
    (marks : Fin (N+1) → (g : G) → {f : Fin M → P g // Function.Injective f})
    (gp : Sigma P) (t : Fin (N+1)) :
    t.val ∈ b643MarkVisits434 P M N marks gp ↔ ∃ j, (marks t gp.1).val j = gp.2 := by
  simp only [b643MarkVisits434,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨s,hs,hst⟩
    have he : s=t := Fin.ext hst
    simpa only [he] using hs
  · intro h
    exact ⟨t,h,rfl⟩

private theorem b643_family_damping (M N : ℕ) (q : ℝ)
    (marks : Fin (N+1) → (g : G) → {f : Fin M → P g // Function.Injective f})
    (states : Fin (N+1) → Green64SmallHaar.GroupState P mod M)
    (off : ℕ → ℤ) (c : MemoryIndependentBIGTorus P mod)
    (hm : ∀ t g, Green64SmallHaar.marks (mod g) M (states t g) = (marks t g).val)
    (hc : ∀ t g p, Green64SmallHaar.residues (mod g) M (states t g) p =
      c g p+(off t.val : ZMod (mod g p))) :
    (∏ t : Fin (N+1), ∏ g : G, sourceVisitQ q N t.val ^
      (Green64SmallHaar.omega (mod g) (Green64SmallHaar.residues (mod g) M (states t g))-M)) =
    memoryIndBIGPhysicalAnchorIntegrand P mod (sourceVisitEta q N) off
      (b643MarkVisits434 P M N marks) (N+1) c := by
  let A := b643MarkVisits434 P M N marks
  unfold memoryIndBIGPhysicalAnchorIntegrand
  rw [Finset.prod_comm]
  conv_rhs => rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro g hg
  let act (t : Fin (N+1)) : Finset (P g) := (Finset.univ : Finset (Fin M)).image (marks t g).val
  let C (t : Fin (N+1)) := Green64SmallHaar.residues (mod g) M (states t g)
  have hl (t : Fin (N+1)) : sourceVisitQ q N t.val ^ (Green64SmallHaar.omega (mod g) (C t)-M) =
      ∏ p : P g, if p ∈ act t then (1:ℝ) else if C t p=0 then sourceVisitQ q N t.val else 1 := by
    have hs : act t ⊆ Green64SmallHaar.zeroCoordSet (mod g) (C t) := by
      intro p hp
      obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hp
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      rw [← he,← hm t g]
      exact Green64SmallHaar.marked_zero (mod g) M (states t g) j
    have hcard : (act t).card=M := by
      unfold act
      rw [Finset.card_image_of_injective _ (marks t g).property]
      simp
    simpa only [Green64SmallHaar.omega,Green64SmallHaar.zeroCoordSet,
      Finset.mem_filter,Finset.mem_univ,true_and] using
      (memory_generic_marked_zero_power_product
        (Green64SmallHaar.zeroCoordSet (mod g) (C t)) (act t) hs M hcard (sourceVisitQ q N t.val))
  calc
    _ = ∏ t : Fin (N+1), ∏ p : P g, if p ∈ act t then (1:ℝ)
        else if C t p=0 then sourceVisitQ q N t.val else 1 := by
      apply Finset.prod_congr rfl
      intro t ht
      exact hl t
    _ = ∏ p : P g, ∏ t : Fin (N+1), if p ∈ act t then (1:ℝ)
        else if C t p=0 then sourceVisitQ q N t.val else 1 := Finset.prod_comm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      have hact : ∀ i ∈ A ⟨g,p⟩, c g p+(off i : ZMod (mod g p))=0 := by
        intro i hi
        obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hi
        obtain ⟨j,hj⟩ := (Finset.mem_filter.mp ht).2
        change (marks t g).val j=p at hj
        calc
          _ = C t p := (hc t g p).symm
          _ = 0 := by
            rw [← hj,← hm t g]
            exact Green64SmallHaar.marked_zero (mod g) M (states t g) j
      rw [ite_eq_left hact,← Fin.prod_univ_eq_prod_range]
      apply Finset.prod_congr rfl
      intro t ht
      have hmem : t.val ∈ A ⟨g,p⟩ ↔ p ∈ act t := by
        rw [b643_mark_visit_mem434 P M N marks]
        simp only [act,Finset.mem_image,Finset.mem_univ,true_and]
      by_cases hpact : p ∈ act t
      · rw [ite_eq_left hpact,ite_eq_left (hmem.mpr hpact)]
      · have hct : C t p=c g p+(off t.val : ZMod (mod g p)) := hc t g p
        rw [ite_eq_right hpact,ite_eq_right (fun h => hpact (hmem.mp h)),hct]
        by_cases hz : c g p+(off t.val : ZMod (mod g p))=0
        · rw [ite_eq_left hz,ite_eq_left hz]
          change sourceVisitQ q N t.val=1-(1-sourceVisitQ q N t.val)*1
          ring
        · rw [ite_eq_right hz,ite_eq_right hz,mul_zero,sub_zero]

private theorem b643_family_integrand_zero (M N : ℕ) (q : ℝ)
    (marks : Fin (N+1) → (g : G) → {f : Fin M → P g // Function.Injective f})
    (off : ℕ → ℤ) (c : MemoryIndependentBIGTorus P mod)
    (ha : ¬ ∀ (t : Fin (N+1)) (g : G) (j : Fin M),
      c g ((marks t g).val j)+(off t.val : ZMod (mod g ((marks t g).val j)))=0) :
    memoryIndBIGPhysicalAnchorIntegrand P mod (sourceVisitEta q N) off
      (b643MarkVisits434 P M N marks) (N+1) c=0 := by
  obtain ⟨t,ht⟩ := not_forall.mp ha
  obtain ⟨g,hg⟩ := not_forall.mp ht
  obtain ⟨j,hj⟩ := not_forall.mp hg
  let gp : Sigma P := ⟨g,(marks t g).val j⟩
  unfold memoryIndBIGPhysicalAnchorIntegrand
  apply Finset.prod_eq_zero (Finset.mem_univ gp)
  apply ite_eq_right
  intro hall
  exact hj (hall t.val ((b643_mark_visit_mem434 P M N marks gp t).mpr ⟨j,rfl⟩))

private theorem b643_family_integrand_nonneg (N : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (off : ℕ → ℤ) (A : Sigma P → Finset ℕ) (c : MemoryIndependentBIGTorus P mod) :
    0 ≤ memoryIndBIGPhysicalAnchorIntegrand P mod (sourceVisitEta q N) off A (N+1) c := by
  unfold memoryIndBIGPhysicalAnchorIntegrand
  apply Finset.prod_nonneg
  intro gp hgp
  split_ifs with ha
  · apply Finset.prod_nonneg
    intro t ht
    split_ifs with hact hz
    · norm_num
    · have hh : 0 ≤ sourceVisitQ q N t := by
        unfold sourceVisitQ
        split_ifs <;> positivity
      change 0 ≤ 1-(1-sourceVisitQ q N t)*1
      linarith
    · simp
  · exact le_rfl
end Family

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Literal product of all SMALL and BIG prime zero-coordinate factors.
All forced marked hits and all inactive visit damping are retained. -/
def b643AllPrimeAnchorIntegrand434 {N : ℕ} (q : ℝ)
    (ω : B643AllPrimePath434 SP BP J ell m patterns N) (k : ℤ)
    (c : B643AllPrimeAnchor434 SP smallMod BP bigMod) : ℝ :=
  memoryIndBIGPhysicalAnchorIntegrand SP smallMod (sourceVisitEta q N)
    (b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k)
    (b643MarkVisits434 SP (J+ell) N ω.1) (N+1) c.1 *
  memoryIndBIGPhysicalAnchorIntegrand BP bigMod (sourceVisitEta q N)
    (b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k)
    (b643MarkVisits434 BP (J+ell) N ω.2.1) (N+1) c.2

/-- Exact all-prime anchored damping identity, now including the original
SMALL states as well as BIG. No residue remains in the frozen coefficient. -/
theorem b643_all_prime_anchor_damping434 {N : ℕ} (q : ℝ)
    (ω : B643AllPrimePath434 SP BP J ell m patterns N) (k : ℤ)
    (c : B643AllPrimeAnchor434 SP smallMod BP bigMod)
    (ha : b643AllPrimeAnchorAllowed434 SP smallMod BP bigMod J ell m patterns ω k c) :
    b643AllPrimeVisitDamping434 SP smallMod BP bigMod J ell q
      (b643AllPrimeAnchoredStates434 SP smallMod BP bigMod J ell m patterns ω k c ha) =
    (b643AllPrimeAnchorIntegrand434 SP smallMod BP bigMod J ell m patterns q ω k c : ℂ) := by
  let states := b643AllPrimeAnchoredStates434 SP smallMod BP bigMod J ell m patterns ω k c ha
  have hs := b643_family_damping SP smallMod (J+ell) N q ω.1 (fun t => (states t).1)
    (b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k) c.1
    (fun _ _ => rfl) (fun _ _ _ => rfl)
  have hb := b643_family_damping BP bigMod (J+ell) N q ω.2.1 (fun t => (states t).2)
    (b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k) c.2
    (fun _ _ => rfl) (fun _ _ _ => rfl)
  have hh := congrArg Complex.ofReal (congrArg₂ (fun a b : ℝ => a*b) hs hb)
  simpa only [b643AllPrimeVisitDamping434,b643AllPrimeAnchorIntegrand434,
    Complex.ofReal_mul,Complex.ofReal_prod] using hh

theorem b643_all_prime_integrand_zero434 {N : ℕ} (q : ℝ)
    (ω : B643AllPrimePath434 SP BP J ell m patterns N) (k : ℤ)
    (c : B643AllPrimeAnchor434 SP smallMod BP bigMod)
    (ha : ¬ b643AllPrimeAnchorAllowed434 SP smallMod BP bigMod J ell m patterns ω k c) :
    b643AllPrimeAnchorIntegrand434 SP smallMod BP bigMod J ell m patterns q ω k c=0 := by
  unfold b643AllPrimeAnchorAllowed434 at ha
  unfold b643AllPrimeAnchorIntegrand434
  by_cases hs : ∀ (t : Fin (N+1)) (g : SG) (j : Fin (J+ell)), c.1 g ((ω.1 t g).val j)+
      (b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k t.val :
        ZMod (smallMod g ((ω.1 t g).val j)))=0
  · have hb := fun h => ha ⟨hs,h⟩
    rw [b643_family_integrand_zero BP bigMod (J+ell) N q ω.2.1 _ c.2 hb,mul_zero]
  · rw [b643_family_integrand_zero SP smallMod (J+ell) N q ω.1 _ c.1 hs,zero_mul]

theorem b643_all_prime_integrand_nonneg434 {N : ℕ} (q : ℝ) (hq : 0 ≤ q)
    (ω : B643AllPrimePath434 SP BP J ell m patterns N) (k : ℤ)
    (c : B643AllPrimeAnchor434 SP smallMod BP bigMod) :
    0 ≤ b643AllPrimeAnchorIntegrand434 SP smallMod BP bigMod J ell m patterns q ω k c :=
  mul_nonneg (b643_family_integrand_nonneg SP smallMod N q hq _ _ c.1)
    (b643_family_integrand_nonneg BP bigMod N q hq _ _ c.2)

/-- All original transported damping equals the complete-prime integrand
at the actual pair of initial anchors, including zero-weight arrays. -/
theorem b643_all_prime_transport_damping434 {N : ℕ} (q : ℝ) (k : ℤ)
    (states : Fin (N+1) → MemoryIndependentState SP smallMod BP bigMod J ell)
    (frames : Fin N → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns)
    (ht : ∀ i, b643AllPrimeRowTransport434 SP smallMod BP bigMod J ell m patterns states frames k i) :
    b643AllPrimeVisitDamping434 SP smallMod BP bigMod J ell q states =
    (b643AllPrimeAnchorIntegrand434 SP smallMod BP bigMod J ell m patterns q
      (b643AllPrimePathOf434 SP smallMod BP bigMod J ell m patterns states frames) k
      ((fun g => Green64SmallHaar.residues (smallMod g) (J+ell) ((states 0).1 g)),
       (fun g => Green64SmallHaar.residues (bigMod g) (J+ell) ((states 0).2 g))) : ℂ) := by
  let e := b643AllPrimeTransportEquiv434 SP smallMod BP bigMod J ell m patterns N k
  let sf : {sf : ((Fin (N+1) → MemoryIndependentState SP smallMod BP bigMod J ell) ×
      (Fin N → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns)) //
      ∀ i, b643AllPrimeRowTransport434 SP smallMod BP bigMod J ell m patterns sf.1 sf.2 k i} :=
    ⟨(states,frames),ht⟩
  have hh := b643_all_prime_anchor_damping434 SP smallMod BP bigMod J ell m patterns q
    (e sf).val.1 k (e sf).val.2 (e sf).property
  have hr := congrArg (fun a => a.val.1) (e.symm_apply_apply sf)
  change b643AllPrimeAnchoredStates434 SP smallMod BP bigMod J ell m patterns
    (e sf).val.1 k (e sf).val.2 (e sf).property=states at hr
  rw [hr] at hh
  exact hh
end Green64FullPhysicalE

end

end

