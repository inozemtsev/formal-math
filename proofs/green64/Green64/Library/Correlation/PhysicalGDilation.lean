module

public import Green64.Library.Correlation.PhysicalReturnGSchur
public import Green64.Library.Correlation.Part044

@[expose] public section

/-!
# Correlation / PhysicalGDilation

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalPhysicalGDilation -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64PhysicalEdge Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 600000

private theorem count_monomial (k alpha chi V m : ℂ)
    (j z a b : ℕ) (ha : a ≤ j) :
    k^j * (alpha^a * chi^(z-a) * (alpha*(k^2*V))^b * m) =
      ((alpha*k)^a * chi^(z-a) * (alpha*k*V)^b * m) * k^(j-a+b) := by
  have hj : j=(j-a)+a := (Nat.sub_add_cancel ha).symm
  rw [hj]
  simp only [Nat.add_sub_cancel,pow_add,mul_pow,pow_two]
  ring

private theorem piece_card {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p,NeZero (modulus p)]
    (old : Multiset (Atom P modulus)) (hn : old.Nodup)
    (d : SourceOriginalGroupPrimeBirthChoice434 modulus
      (old.toFinset.filter (fun z => z.2=0))) :
    (sourceOriginalGhostPiecePending434 modulus old.toFinset d.1.1 d.2).card =
      old.card-d.1.1.card+d.2.card := by
  have hd : d.1.1 ⊆ old.toFinset :=
    (Finset.mem_powerset.mp d.1.2).trans (Finset.filter_subset _ _)
  simp only [sourceOriginalGhostPiecePending434,Multiset.card_add,Multiset.card_sum,
    Multiset.card_singleton,Finset.sum_const,nsmul_eq_mul,mul_one]
  rw [Finset.card_sdiff_of_subset hd,Multiset.toFinset_card_of_nodup hn]
  simp

private theorem scalar_dilation
    (q rho u kappa V : ℝ) (N i : ℕ)
    (hR : sourceVisitQ q N i/rho^2=u)
    (hB : sourceVisitEta q N i/rho=(1-u)*kappa)
    (j z a b : ℕ) (mass : ℂ) (ha : a ≤ j) :
    (kappa:ℂ)^j *
      ((-(sourceVisitEta u 0 1:ℂ)/(1:ℂ))^a *
        ((sourceVisitQ u 0 1:ℂ)/(1:ℂ)^2)^(z-a) *
        (-(sourceVisitEta u 0 1:ℂ)*(kappa^2*V:ℝ)/(1:ℂ))^b * mass) =
      ((-(sourceVisitEta q N i:ℂ)/(rho:ℂ))^a *
        ((sourceVisitQ q N i:ℂ)/(rho:ℂ)^2)^(z-a) *
        (-(sourceVisitEta q N i:ℂ)*(V:ℂ)/(rho:ℂ))^b * mass) *
        (kappa:ℂ)^(j-a+b) := by
  have hRc : (sourceVisitQ q N i:ℂ)/(rho:ℂ)^2=(u:ℂ) := by exact_mod_cast hR
  have hBc : -(sourceVisitEta q N i:ℂ)/(rho:ℂ)=
      (-(1-(u:ℂ)))*(kappa:ℂ) := by
    have h : (sourceVisitEta q N i:ℂ)/(rho:ℂ)=(1-(u:ℂ))*(kappa:ℂ) := by
      exact_mod_cast hB
    simpa only [neg_div,neg_mul] using congrArg Neg.neg h
  have hBcV : -(sourceVisitEta q N i:ℂ)*(V:ℂ)/(rho:ℂ)=
      (-(1-(u:ℂ)))*(kappa:ℂ)*(V:ℂ) := by
    calc
      _ = (-(sourceVisitEta q N i:ℂ)/(rho:ℂ))*(V:ℂ) := by ring
      _ = _ := by rw [hBc]
  have hi0 : sourceVisitEta u 0 1=1-u := by norm_num [sourceVisitEta,sourceVisitQ]
  have hi1 : sourceVisitQ u 0 1=u := by norm_num [sourceVisitQ]
  simp only [hi0,hi1,one_pow,div_one,hRc,hBc,hBcV,
    Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_pow]
  exact count_monomial (kappa:ℂ) (-(1-(u:ℂ))) (u:ℂ) (V:ℂ)
    mass j z a b ha

private theorem group_dilation {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p,NeZero (modulus p)]
    (S : Finset (Atom P modulus))
    (q rho u kappa V : ℝ) (N i : ℕ)
    (hR : sourceVisitQ q N i/rho^2=u)
    (hB : sourceVisitEta q N i/rho=(1-u)*kappa)
    (mu : P → ℝ) (d : SourceOriginalGroupPrimeBirthChoice434 modulus S)
    (j : ℕ) (ha : d.1.1.card ≤ j) :
    (kappa:ℂ)^j *
      sourceOriginalGroupPrimeBirthWeight434 modulus S
        (-(sourceVisitEta u 0 1:ℂ)/(1:ℂ))
        ((sourceVisitQ u 0 1:ℂ)/(1:ℂ)^2)
        (-(sourceVisitEta u 0 1:ℂ)*(kappa^2*V:ℝ)/(1:ℂ))
        (fun p => (mu p:ℂ)) d =
    sourceOriginalGroupPrimeBirthWeight434 modulus S
        (-(sourceVisitEta q N i:ℂ)/(rho:ℂ))
        ((sourceVisitQ q N i:ℂ)/(rho:ℂ)^2)
        (-(sourceVisitEta q N i:ℂ)*(V:ℂ)/(rho:ℂ))
        (fun p => (mu p:ℂ)) d * (kappa:ℂ)^(j-d.1.1.card+d.2.card) :=
  scalar_dilation q rho u kappa V N i hR hB j S.card d.1.1.card d.2.card
    (∏ p ∈ d.2,(mu p:ℂ)) ha

private theorem delete_card_le {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p,NeZero (modulus p)]
    (old : Multiset (Atom P modulus)) (hn : old.Nodup)
    (S : Finset (Atom P modulus)) (hS : S ⊆ old.toFinset)
    (d : SourceOriginalGroupPrimeBirthChoice434 modulus S) :
    d.1.1.card ≤ old.card :=
  (Finset.card_le_card ((Finset.mem_powerset.mp d.1.2).trans hS)).trans_eq
    (Multiset.toFinset_card_of_nodup hn)

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ)

def sourceOriginalPendingDilation434 (kappa : ℝ)
    (y : FullPhysicalOutput SP sm BP bm M) : ℝ :=
  kappa^(∑ g,(y.2 g).2.card)

private theorem dilation_as_prod (kappa : ℝ)
    (z : FullPhysicalOutput SP sm BP bm M) :
    (sourceOriginalPendingDilation434 SP sm BP bm M kappa z:ℂ) =
      ∏ g,(kappa:ℂ)^((z.2 g).2.card) := by
  simp only [sourceOriginalPendingDilation434,Complex.ofReal_pow,
    Finset.prod_pow_eq_pow_sum]

private theorem lift_output (y : FullPhysicalOutput SP sm BP bm M)
    (d : SourceOriginalPhysicalGhostPrimeBirthWitness434 SP sm BP bm M y) (g : BG) :
    ((sourceOriginalPhysicalGhostAtomOutput434 SP sm BP bm M y
      (sourceOriginalPhysicalGhostPrimeBirthLift434 SP sm BP bm M y d)).2 g).2 =
    sourceOriginalGhostPiecePending434 (bm g) (y.2 g).2.toFinset (d g).1.1 (d g).2 := by
  change (∑ z ∈ (y.2 g).2.toFinset \ (d g).1.1,({z}:Multiset (Atom (BP g) (bm g)))) +
    (∑ z ∈ (d g).2.map (sourceOriginalZeroAtomEmbedding434 (bm g)),
      ({z}:Multiset (Atom (BP g) (bm g)))) = _
  rw [Finset.sum_map]
  rfl

private theorem coefficient_dilation
    (q rho u kappa : ℝ) (N i : ℕ)
    (hR : sourceVisitQ q N i/rho^2=u)
    (hB : sourceVisitEta q N i/rho=(1-u)*kappa)
    (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP sm BP bm M)
    (hn : ∀ g,((y.2 g).2).Nodup)
    (d : SourceOriginalPhysicalGhostPrimeBirthWitness434 SP sm BP bm M y) :
    (sourceOriginalPendingDilation434 SP sm BP bm M kappa y:ℂ) *
      sourceOriginalPhysicalGhostPrimeBirthCoefficient434 SP sm BP bm M
        u 1 0 1 (fun g => kappa^2*V g) mu y d =
    sourceOriginalPhysicalGhostPrimeBirthCoefficient434 SP sm BP bm M
        q rho N i V mu y d *
      (sourceOriginalPendingDilation434 SP sm BP bm M kappa
        (sourceOriginalPhysicalGhostAtomOutput434 SP sm BP bm M y
          (sourceOriginalPhysicalGhostPrimeBirthLift434 SP sm BP bm M y d)):ℂ) := by
  rw [dilation_as_prod,dilation_as_prod]
  unfold sourceOriginalPhysicalGhostPrimeBirthCoefficient434
  rw [←Finset.prod_mul_distrib,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g hg
  rw [lift_output SP sm BP bm M y d g,piece_card (bm g) (y.2 g).2 (hn g) (d g)]
  exact group_dilation (bm g) _ q rho u kappa (V g) N i hR hB
    (mu g) (d g) (y.2 g).2.card
    (delete_card_le (bm g) (y.2 g).2 (hn g) _ (Finset.filter_subset _ _) (d g))

/-- Exact diagonal similarity of the original physical G for admissible
rho to a rho=1 auxiliary G. The function is joint in all original data;
there is no bound on its modulus. -/
theorem source_original_PHYSICAL_G_dilation434
    (q rho u kappa : ℝ) (N i : ℕ)
    (hR : sourceVisitQ q N i/rho^2=u)
    (hB : sourceVisitEta q N i/rho=(1-u)*kappa)
    (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (hn : ∀ g,((y.2 g).2).Nodup)
    (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ) :
    (sourceOriginalPendingDilation434 SP sm BP bm M kappa y:ℂ) *
      sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm M
        u 1 0 1 (fun g => kappa^2*V g) mu y seen F =
    sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm M
      q rho N i V mu y seen
      (fun out st => (sourceOriginalPendingDilation434 SP sm BP bm M kappa out:ℂ)*F out st) := by
  unfold sourceOriginalPhysicalGhostUnseenPrimeRow434
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  split_ifs with hd
  · rw [←mul_assoc,coefficient_dilation SP sm BP bm M q rho u kappa N i hR hB V mu y hn d]
    ring
  · simp only [mul_zero]

variable (J ell : ℕ) (cap : BG → ℕ)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

private theorem actual_nodup (a : H) : ∀ g,((a.val.1.2 g).2).Nodup := by
  have ha := (source_original_ACTUAL_signed_history_mem_iff434
    SP sm BP bm J ell cap a.val.1 a.val.2).mp a.property
  obtain ⟨x,hx,hproj⟩ := Finset.mem_image.mp ha.1
  have hr : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap x) a.val.2 := by
    rw [hproj]
    exact ha.2.2
  have hn := (source_original_PHYSICAL_reachable_pending434
    SP sm BP bm (J+ell) cap x a.val.2 hr).1
  intro g
  have he : fockMultiset (x.2 g).2=(a.val.1.2 g).2 :=
    congrArg (fun y : FullPhysicalOutput SP sm BP bm (J+ell) => (y.2 g).2) hproj
  rw [←he]
  exact (hn g).of_map (fun z => z.1)

/-- The similarity is on the actual finite physical matrix, not an
unidentified background process. Both matrices use the same mu and seen. -/
theorem source_original_ACTUAL_G_dilation434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho u kappa : ℝ) (N i : ℕ)
    (hR : sourceVisitQ q N i/rho^2=u)
    (hB : sourceVisitEta q N i/rho=(1-u)*kappa)
    (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (a b : H) :
    (sourceOriginalPendingDilation434 SP sm BP bm (J+ell) kappa a.val.1:ℂ) *
      sourceOriginalActualSignedGhostMatrix434 SP sm BP bm J ell cap
        u 1 0 1 (fun g => kappa^2*V g) mu a b =
    sourceOriginalActualSignedGhostMatrix434 SP sm BP bm J ell cap
        q rho N i V mu a b *
      (sourceOriginalPendingDilation434 SP sm BP bm (J+ell) kappa b.val.1:ℂ) := by
  let F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ :=
    fun out seen => if (out,seen)=b.val then 1 else 0
  have hf (c : H) : F c.val.1 c.val.2=if c=b then 1 else 0 := by
    dsimp only [F]
    by_cases hc : c=b
    · subst c
      simp
    · have hv : (c.val.1,c.val.2) ≠ b.val := fun h => hc (Subtype.ext h)
      rw [if_neg hv,if_neg hc]
  have ha := source_original_ACTUAL_original_G_matrix_exact434
    SP sm BP bm J ell cap hi hcap u 1 0 1 Vs (fun g => kappa^2*V g) mu hVs hmu F a
  have hb := source_original_ACTUAL_original_G_matrix_exact434
    SP sm BP bm J ell cap hi hcap q rho N i Vs V mu hVs hmu
    (fun out st => (sourceOriginalPendingDilation434 SP sm BP bm (J+ell) kappa out:ℂ)*F out st) a
  have h := source_original_PHYSICAL_G_dilation434 SP sm BP bm (J+ell)
    q rho u kappa N i hR hB V mu a.val.1 a.val.2
    (actual_nodup SP sm BP bm J ell cap a) F
  rw [ha,hb] at h
  simp_rw [hf,mul_ite,mul_one,mul_zero] at h
  simpa only [Finset.sum_ite_eq',Finset.mem_univ,ite_true] using h

/-- Exact isometric density transport. Auxiliary V is scaled only after
this identity is proved; the resulting energy statement returns to pi. -/
theorem source_original_ACTUAL_density_dilation434
    (kappa : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (a : H) :
    sourceOriginalActualSignedTrueFockDensity434 SP sm BP bm J ell cap
        Vs (fun g => kappa^2*V g) mu a =
      sourceOriginalActualSignedTrueFockDensity434 SP sm BP bm J ell cap Vs V mu a *
        (sourceOriginalPendingDilation434 SP sm BP bm (J+ell) kappa a.val.1)^2 := by
  simp only [sourceOriginalActualSignedTrueFockDensity434,sourceOriginalMemorySectorDensity434,
    sourceOriginalPendingDilation434,mul_pow,Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum,←pow_mul]
  rw [←Finset.mul_sum,Nat.mul_comm 2]
  ring

end Green64Analytic.CorrelationSquare

end

end

