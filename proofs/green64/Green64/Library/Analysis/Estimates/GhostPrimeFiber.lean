module

public import Green64.Library.Correlation.PhysicalGhostOutputSeparation

@[expose] public section

/-!
# Analysis / Estimates / GhostPrimeFiber

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalGhostPrimeFiber -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- An exact powerset/fibre equivalence. No summand is duplicated. -/
def sourceOriginalSubsetFiberEquiv434
    {U P : Type} [Fintype U] [DecidableEq U] [Fintype P] [DecidableEq P]
    (S : Finset U) (f : U → P) :
    {A : Finset U // A ∈ S.powerset} ≃
      ((p : P) → {A : Finset U // A ∈ (S.filter (fun z => f z=p)).powerset}) where
  toFun A p := ⟨A.1.filter (fun z => f z=p),Finset.mem_powerset.mpr (by
    intro z hz
    exact Finset.mem_filter.mpr ⟨(Finset.mem_powerset.mp A.2) (Finset.mem_filter.mp hz).1,
      (Finset.mem_filter.mp hz).2⟩)⟩
  invFun d := ⟨Finset.univ.biUnion (fun p => (d p).1),Finset.mem_powerset.mpr (by
    intro z hz
    obtain ⟨p,_,hp⟩ := Finset.mem_biUnion.mp hz
    exact (Finset.mem_filter.mp ((Finset.mem_powerset.mp (d p).2) hp)).1)⟩
  left_inv A := by
    apply Subtype.ext
    ext z
    simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_filter]
    constructor
    · rintro ⟨p,hz,_⟩
      exact hz
    · intro hz
      exact ⟨f z,hz,rfl⟩
  right_inv d := by
    funext p
    apply Subtype.ext
    ext z
    constructor
    · intro hz
      obtain ⟨hz,hp⟩ := Finset.mem_filter.mp hz
      obtain ⟨q,_,hq⟩ := Finset.mem_biUnion.mp hz
      have hq' := (Finset.mem_filter.mp ((Finset.mem_powerset.mp (d q).2) hq)).2
      have he : q=p := hq'.symm.trans hp
      exact Eq.mp (congrArg (fun t => z ∈ (d t).1) he) hq
    · intro hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨p,Finset.mem_univ _,hz⟩,
        (Finset.mem_filter.mp ((Finset.mem_powerset.mp (d p).2) hz)).2⟩

theorem source_original_SUBSET_fiber_card434
    {U P : Type} [DecidableEq U] [Fintype P] [DecidableEq P]
    (S : Finset U) (f : U → P) :
    (∑ p : P,(S.filter (fun z => f z=p)).card)=S.card := by
  simpa using Finset.sum_card_fiberwise_eq_card_filter S (Finset.univ : Finset P) f

private theorem fiberSdiff
    {U P : Type} [DecidableEq U] [DecidableEq P]
    (S A : Finset U) (f : U → P) (p : P) :
    (S.filter (fun z => f z=p)) \ (A.filter (fun z => f z=p)) =
      (S \ A).filter (fun z => f z=p) := by
  ext z
  simp only [Finset.mem_sdiff,Finset.mem_filter]
  tauto

private theorem subsetCardSdiff
    {U : Type} [DecidableEq U] (S A : Finset U) (h : A ⊆ S) :
    (S \ A).card=S.card-A.card := by
  rw [Finset.card_sdiff,Finset.inter_eq_left.mpr h]

theorem source_original_SUBSET_fiber_retained_card434
    {U P : Type} [DecidableEq U] [Fintype P] [DecidableEq P]
    (S A : Finset U) (h : A ⊆ S) (f : U → P) :
    (∑ p : P,((S.filter (fun z => f z=p)).card-(A.filter (fun z => f z=p)).card)) =
      S.card-A.card := by
  have he (p : P) :
      (S.filter (fun z => f z=p)).card-(A.filter (fun z => f z=p)).card =
        ((S \ A).filter (fun z => f z=p)).card := by
    rw [←fiberSdiff S A f p,subsetCardSdiff]
    intro z hz
    exact Finset.mem_filter.mpr ⟨h (Finset.mem_filter.mp hz).1,(Finset.mem_filter.mp hz).2⟩
  simp_rw [he]
  rw [source_original_SUBSET_fiber_card434,subsetCardSdiff S A h]

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]

abbrev SourceOriginalPrimeFiberChoice434 (S : Finset (Atom P modulus)) (pool : Finset P) :=
  (p : P) → SourceOriginalRestrictedPrimeBirthChoice434 modulus
    (S.filter (fun z => z.1=p)) (pool.filter (fun t => t=p))

def sourceOriginalPrimeFiberEquiv434 (S : Finset (Atom P modulus)) (pool : Finset P) :
    SourceOriginalRestrictedPrimeBirthChoice434 modulus S pool ≃
      SourceOriginalPrimeFiberChoice434 modulus S pool :=
  (Equiv.prodCongr
    (sourceOriginalSubsetFiberEquiv434 S (fun z => z.1))
    (sourceOriginalSubsetFiberEquiv434 pool id)).trans
      (sourceOriginalPiPairEquiv434 _ _).symm

/-- Actual signed group G weights factor exactly over prime fibres.
This includes deletion, retention and V*mu birth coefficients. -/
theorem source_original_GROUP_G_prime_fiber_weight434
    (S : Finset (Atom P modulus)) (pool : Finset P)
    (alpha chi gamma : ℂ) (mu : P → ℂ)
    (d : SourceOriginalRestrictedPrimeBirthChoice434 modulus S pool) :
    sourceOriginalGroupPrimeBirthWeight434 modulus S alpha chi gamma mu
      (sourceOriginalRestrictedPrimeBirthLift434 modulus S pool d) =
    ∏ p : P,sourceOriginalGroupPrimeBirthWeight434 modulus
      (S.filter (fun z => z.1=p)) alpha chi gamma mu
      (sourceOriginalRestrictedPrimeBirthLift434 modulus _ _
        (sourceOriginalPrimeFiberEquiv434 modulus S pool d p)) := by
  change alpha^d.1.1.card * chi^(S.card-d.1.1.card) *
      gamma^d.2.1.card * (∏ t ∈ d.2.1,mu t) =
    ∏ p : P,(alpha^(d.1.1.filter (fun z => z.1=p)).card *
      chi^((S.filter (fun z => z.1=p)).card-(d.1.1.filter (fun z => z.1=p)).card) *
      gamma^(d.2.1.filter (fun t => t=p)).card *
      (∏ t ∈ d.2.1.filter (fun t => t=p),mu t))
  simp only [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,
    source_original_SUBSET_fiber_card434,
    source_original_SUBSET_fiber_retained_card434 S d.1.1 (Finset.mem_powerset.mp d.1.2),
    Finset.prod_fiberwise]

/-- Exact finite Fubini identity for the original restricted G
choice sum, with its completely joint observation H retained. -/
theorem source_original_GROUP_G_prime_fiber_sum434
    (S : Finset (Atom P modulus)) (pool : Finset P)
    (alpha chi gamma : ℂ) (mu : P → ℂ)
    (H : SourceOriginalRestrictedPrimeBirthChoice434 modulus S pool → ℂ) :
    (∑ d : SourceOriginalRestrictedPrimeBirthChoice434 modulus S pool,
      sourceOriginalGroupPrimeBirthWeight434 modulus S alpha chi gamma mu
        (sourceOriginalRestrictedPrimeBirthLift434 modulus S pool d) * H d) =
    ∑ a : SourceOriginalPrimeFiberChoice434 modulus S pool,
      (∏ p : P,sourceOriginalGroupPrimeBirthWeight434 modulus
        (S.filter (fun z => z.1=p)) alpha chi gamma mu
        (sourceOriginalRestrictedPrimeBirthLift434 modulus _ _ (a p))) *
      H ((sourceOriginalPrimeFiberEquiv434 modulus S pool).symm a) := by
  symm
  apply Fintype.sum_equiv (sourceOriginalPrimeFiberEquiv434 modulus S pool).symm
  intro a
  rw [source_original_GROUP_G_prime_fiber_weight434]
  simp only [Equiv.apply_symm_apply]
end Green64Analytic.CorrelationSquare

end

end

