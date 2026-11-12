module

public import Green64.Library.Weights.Part027
public import Green64.Library.Weights.SourceEFrameRow
public import Green64.Library.Correlation.MemoryFullChainRhoInvariant

@[expose] public section

/-!
# Weights / Part028

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalSourceGOrbit -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64MemoryGhostOp
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ) (cap : BG → ℕ)

variable (x y : FullPhysicalState SP sm BP bm M cap)
variable (e : (g : BG) → Fin (fockToList (y.2 g).2).length ≃ Fin (fockToList (x.2 g).2).length)
variable (he : ∀ g j,(fockToList (x.2 g).2).get (e g j)=(fockToList (y.2 g).2).get j)

def sourceOriginalFullGhostSetReindex434 :
    SourceOriginalPhysicalGhostSetWitness434 SP sm BP bm M cap x ≃
      SourceOriginalPhysicalGhostSetWitness434 SP sm BP bm M cap y :=
  Equiv.piCongrRight (fun g => sourceOriginalGhostSetReindex434
    (fockToList (x.2 g).2) (fockToList (y.2 g).2)
    (fun z : Atom (BP g) (bm g) => z.2=0) (e g) (he g))

theorem source_original_PHYSICAL_G_reindex_births434
    (d : SourceOriginalPhysicalGhostSetWitness434 SP sm BP bm M cap x) :
    sourceOriginalPhysicalGhostSetBirths434 SP sm BP bm M cap y
      (sourceOriginalFullGhostSetReindex434 SP sm BP bm M cap x y e he d) =
    sourceOriginalPhysicalGhostSetBirths434 SP sm BP bm M cap x d := rfl

theorem source_original_PHYSICAL_G_reindex_output434
    (hxy : physicalFockProjection SP sm BP bm M cap x =
      physicalFockProjection SP sm BP bm M cap y)
    (d : SourceOriginalPhysicalGhostSetWitness434 SP sm BP bm M cap x) :
    sourceOriginalPhysicalGhostSetOutput434 SP sm BP bm M cap y
      (sourceOriginalFullGhostSetReindex434 SP sm BP bm M cap x y e he d) =
    sourceOriginalPhysicalGhostSetOutput434 SP sm BP bm M cap x d := by
  apply Prod.ext
  · change y.1=x.1
    exact congrArg (fun z : FullPhysicalOutput SP sm BP bm M => z.1) hxy.symm
  · funext g
    apply Prod.ext
    · change (y.2 g).1=(x.2 g).1
      exact congrArg (fun z : FullPhysicalOutput SP sm BP bm M => (z.2 g).1) hxy.symm
    · change memoryTupleBag
          (fun j : {j : Fin (fockToList (y.2 g).2).length // j ∉
              (e g).symm.finsetCongr (d g).1.1} => (fockToList (y.2 g).2).get j) +
          (∑ z ∈ (d g).2,({z}:Multiset (Atom (BP g) (bm g)))) =
        memoryTupleBag
          (fun j : {j : Fin (fockToList (x.2 g).2).length // j ∉ (d g).1.1} =>
            (fockToList (x.2 g).2).get j) +
          (∑ z ∈ (d g).2,({z}:Multiset (Atom (BP g) (bm g))))
      rw [source_original_G_reindex_survivor_bag434
        (fockToList (x.2 g).2) (fockToList (y.2 g).2) (e g) (he g)]

theorem source_original_PHYSICAL_G_reindex_coefficient434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (d : SourceOriginalPhysicalGhostSetWitness434 SP sm BP bm M cap x) :
    sourceOriginalPhysicalGhostSetCoefficient434 SP sm BP bm M cap q rho N i V mu y
      (sourceOriginalFullGhostSetReindex434 SP sm BP bm M cap x y e he d) =
    sourceOriginalPhysicalGhostSetCoefficient434 SP sm BP bm M cap q rho N i V mu x d := by
  apply Finset.prod_congr rfl
  intro g hg
  exact source_original_G_reindex_set_coefficient434
    (fockToList (x.2 g).2) (fockToList (y.2 g).2)
    (fun z : Atom (BP g) (bm g) => z.2=0) (e g) (he g) (cap g) _ _ _ _ (d g)

theorem source_original_PHYSICAL_G_reindex_test434
    (hxy : physicalFockProjection SP sm BP bm M cap x =
      physicalFockProjection SP sm BP bm M cap y)
    (seen : Finset ℕ) (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ)
    (d : SourceOriginalPhysicalGhostSetWitness434 SP sm BP bm M cap x) :
    sourceOriginalPhysicalGhostSetTest434 SP sm BP bm M cap y seen F
      (sourceOriginalFullGhostSetReindex434 SP sm BP bm M cap x y e he d) =
    sourceOriginalPhysicalGhostSetTest434 SP sm BP bm M cap x seen F d := by
  unfold sourceOriginalPhysicalGhostSetTest434 sourceOriginalPhysicalGhostSetEligible434
    sourceOriginalPhysicalGhostSetFits434
  rw [source_original_PHYSICAL_G_reindex_births434,
    source_original_PHYSICAL_G_reindex_output434 SP sm BP bm M cap x y e he hxy]

/- Exact full marked G invariance for any actual index transport. Both
cutoffs and the one global numerical birth gate are retained. -/
include he in
theorem source_original_PHYSICAL_MARKED_G_index_transport434
    (hxy : physicalFockProjection SP sm BP bm M cap x =
      physicalFockProjection SP sm BP bm M cap y)
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (seen : Finset ℕ) (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ) :
    physicalGBirthMarkedRow SP sm BP bm M cap q rho N i V mu y seen F =
    physicalGBirthMarkedRow SP sm BP bm M cap q rho N i V mu x seen F := by
  rw [source_original_PHYSICAL_MARKED_G_set_extraction434,
    source_original_PHYSICAL_MARKED_G_set_extraction434]
  symm
  apply Fintype.sum_equiv (sourceOriginalFullGhostSetReindex434 SP sm BP bm M cap x y e he)
  intro d
  rw [source_original_PHYSICAL_G_reindex_coefficient434,
    source_original_PHYSICAL_G_reindex_test434 SP sm BP bm M cap x y e he hxy]

omit e he in
theorem source_original_PHYSICAL_MARKED_G_orbit_invariant434
    (hxy : physicalFockProjection SP sm BP bm M cap x =
      physicalFockProjection SP sm BP bm M cap y)
    (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm M
      (physicalFockProjection SP sm BP bm M cap y) seen)
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ) :
    physicalGBirthMarkedRow SP sm BP bm M cap q rho N i V mu y seen F =
    physicalGBirthMarkedRow SP sm BP bm M cap q rho N i V mu x seen F := by
  have hx : sourceOriginalPhysicalReachable434 SP sm BP bm M
      (physicalFockProjection SP sm BP bm M cap x) seen := by simpa only [hxy] using hy
  have hox := (source_original_PHYSICAL_reachable_pending434 SP sm BP bm M cap x seen hx).1
  have hoy := (source_original_PHYSICAL_reachable_pending434 SP sm BP bm M cap y seen hy).1
  have he (g : BG) := source_original_nodup_list_index_equiv434
    (fockToList (x.2 g).2) (fockToList (y.2 g).2)
    ((hox g).of_map (fun z => z.1)) ((hoy g).of_map (fun z => z.1))
    (congrArg (fun z : FullPhysicalOutput SP sm BP bm M => (z.2 g).2) hxy)
  choose e he using he
  exact source_original_PHYSICAL_MARKED_G_index_transport434
    SP sm BP bm M cap x y e he hxy q rho N i V mu seen F

omit y e he in
theorem source_original_ORBIT_constant_representative434
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (f : FullPhysicalState SP sm BP bm M cap → ℂ)
    (hf : ∀ y,physicalFockProjection SP sm BP bm M cap y =
      physicalFockProjection SP sm BP bm M cap x → f y=f x) :
    fullPhysicalOrbitAverage SP sm BP bm M cap Vs mu f
      (physicalFockProjection SP sm BP bm M cap x) = f x := by
  let out := physicalFockProjection SP sm BP bm M cap x
  have hpos : (physicalOrbitMass SP sm BP bm M cap Vs mu out : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (physicalOrbitMass_pos SP sm BP bm M cap Vs mu hVs hmu out
      (Finset.mem_image.mpr ⟨x,Finset.mem_univ x,rfl⟩)))
  unfold fullPhysicalOrbitAverage
  change (∑ y ∈ (Finset.univ : Finset (FullPhysicalState SP sm BP bm M cap))
      with physicalFockProjection SP sm BP bm M cap y=out,
      (fullPhysicalMass SP sm BP bm M cap Vs mu y : ℂ)*f y) /
      (physicalOrbitMass SP sm BP bm M cap Vs mu out : ℂ)=f x
  have hn : (∑ y ∈ (Finset.univ : Finset (FullPhysicalState SP sm BP bm M cap))
      with physicalFockProjection SP sm BP bm M cap y=out,
      (fullPhysicalMass SP sm BP bm M cap Vs mu y : ℂ)*f y) =
      (physicalOrbitMass SP sm BP bm M cap Vs mu out : ℂ)*f x := by
    unfold physicalOrbitMass
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y hy
    rw [hf y (Finset.mem_filter.mp hy).2]
  rw [hn]
  exact mul_div_cancel_left₀ _ hpos

omit M x y e he in
theorem source_original_SOURCE_SYMMETRIC_G_representative434
    (J ell : ℕ) (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (hx : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap x) seen)
    (q rho : ℝ) (N i : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    physicalMarkedSymmetricG SP sm BP bm J ell cap q rho N i Vs V mu
      (physicalFockProjection SP sm BP bm (J+ell) cap x) seen F =
    physicalGBirthMarkedRow SP sm BP bm (J+ell) cap q rho N i V mu x seen F := by
  apply source_original_ORBIT_constant_representative434
    SP sm BP bm (J+ell) cap x Vs mu hVs hmu
  intro y hy
  exact (source_original_PHYSICAL_MARKED_G_orbit_invariant434
    SP sm BP bm (J+ell) cap y x hy seen hx q rho N i V mu F).symm
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPhysicalCanonical -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ) (cap : BG → ℕ)

/-- A reachable physical output has at most one OLD atom for each BIG
prime label. This is derived from the global numerical birth filter. -/
theorem source_original_REACHABLE_pending_card434
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm M y seen) (g : BG) :
    (y.2 g).2.card ≤ Fintype.card (BP g) := by
  have hl : (y.2 g).2.map (fun z => bm g z.1) ≤
      sourceOriginalPhysicalInventory434 SP sm BP bm M y := by
    apply le_trans (b := sourceOriginalBigInventory434 (bm g) M
      (y.2 g).1 (y.2 g).2) le_add_self
    have hh := Finset.sum_le_sum_of_subset
      (f := fun h : BG => sourceOriginalBigInventory434 (bm h) M
        (y.2 h).1 (y.2 h).2)
      (Finset.singleton_subset_iff.mpr (Finset.mem_univ g))
    simpa only [Finset.sum_singleton,sourceOriginalPhysicalInventory434] using hh
  have hn : (((y.2 g).2.toList).map (fun z => bm g z.1)).Nodup := by
    change (↑(((y.2 g).2.toList).map (fun z => bm g z.1)) : Multiset ℕ).Nodup
    rw [←Multiset.map_coe,Multiset.coe_toList]
    exact Multiset.nodup_of_le hl hy.1
  have hp : (((y.2 g).2.toList).map (fun z => z.1)).Nodup := by
    apply List.Nodup.of_map (bm g)
    simpa only [List.map_map,Function.comp_def] using hn
  simpa only [List.length_map,Multiset.length_toList] using hp.length_le_card

/-- Total canonical OLD representative. The fallback is never used on
the proved reachable sector when the original caps are saturated. -/
def sourceOriginalCanonicalPhysical434
    (y : FullPhysicalOutput SP sm BP bm M) : FullPhysicalState SP sm BP bm M cap :=
  (y.1,fun g => ((y.2 g).1,
    if h : (y.2 g).2.toList.length ≤ cap g then
      sourceOriginalFockFromList434 (y.2 g).2.toList h
    else sourceOriginalFockFromList434 [] (Nat.zero_le _)))

theorem source_original_REACHABLE_canonical_projection434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm M y seen) :
    physicalFockProjection SP sm BP bm M cap
      (sourceOriginalCanonicalPhysical434 SP sm BP bm M cap y) = y := by
  apply Prod.ext
  · rfl
  · funext g
    apply Prod.ext
    · rfl
    · have hc : (y.2 g).2.toList.length ≤ cap g := by
        rw [Multiset.length_toList]
        exact (source_original_REACHABLE_pending_card434 SP sm BP bm M y seen hy g).trans (hcap g)
      change fockMultiset
        (if h : (y.2 g).2.toList.length ≤ cap g then
          sourceOriginalFockFromList434 (y.2 g).2.toList h
        else sourceOriginalFockFromList434 [] (Nat.zero_le _)) = (y.2 g).2
      rw [dif_pos hc]
      change (↑(fockToList (sourceOriginalFockFromList434 (y.2 g).2.toList hc)) :
        Multiset (Atom (BP g) (bm g))) = (y.2 g).2
      rw [source_original_fock_to_from_list434,Multiset.coe_toList]

theorem source_original_REACHABLE_orbit_support434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm M y seen) :
    y ∈ physicalFockOrbitSupport SP sm BP bm M cap := by
  exact Finset.mem_image.mpr ⟨sourceOriginalCanonicalPhysical434 SP sm BP bm M cap y,
    Finset.mem_univ _, source_original_REACHABLE_canonical_projection434
      SP sm BP bm M cap hcap y seen hy⟩

variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

theorem source_original_SOURCE_SYMMETRIC_G_canonical434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen)
    (q rho : ℝ) (N i : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    physicalMarkedSymmetricG SP sm BP bm J ell cap q rho N i Vs V mu y seen F =
    physicalGBirthMarkedRow SP sm BP bm (J+ell) cap q rho N i V mu
      (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap y) seen F := by
  have hp := source_original_REACHABLE_canonical_projection434
    SP sm BP bm (J+ell) cap hcap y seen hy
  have hx : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap
        (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap y)) seen := by
    simpa only [hp] using hy
  have hh := source_original_SOURCE_SYMMETRIC_G_representative434 SP sm BP bm cap J ell
    (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap y) seen hx
    q rho N i Vs V mu hVs hmu F
  simpa only [hp] using hh

theorem source_original_SOURCE_SYMMETRIC_E_canonical434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    physicalOrientedMarkedSymmetricE SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k y seen F =
    physicalOrientedBirthMarkedE SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k
      (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap y) seen F := by
  have hp := source_original_REACHABLE_canonical_projection434
    SP sm BP bm (J+ell) cap hcap y seen hy
  have hx : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap
        (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap y)) seen := by
    simpa only [hp] using hy
  have hh := source_original_SOURCE_SYMMETRIC_E_representative434 SP sm BP bm cap J ell m patterns
    (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap y) seen hx
    q rho Vs V mu hVs hmu K zeta theta o k F
  simpa only [hp] using hh
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryCanonicalChain -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Literal marked source G/E rows on canonical OLD representatives.
There are no internal orbit averages; the joint K and all original
branch sums, orientations, phases, gates and coefficients are unchanged. -/
def sourceOriginalCanonicalGEChain434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ) :
    (remaining start : ℕ) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
  | 0,start,F => fun y seen =>
      physicalGBirthMarkedRow SP sm BP bm (J+ell) cap q rho N start V mu
        (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap y) seen F
  | n+1,start,F => fun y seen =>
      physicalGBirthMarkedRow SP sm BP bm (J+ell) cap q rho N start V mu
        (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap y) seen
        (fun yg sg =>
          physicalOrientedBirthMarkedE SP sm BP bm J ell m cap patterns
            q rho Vs V mu
            (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
            zeta theta (physicalAlternatingSign start) k
            (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg
            (sourceOriginalCanonicalGEChain434 q rho Vs V mu K zeta theta k N n (start+1) F))

/-- Exact chain descent, uniform in all finite carriers, depths and joint
terminal tests. Only physical positivity and the original saturated caps
are needed in addition to the proved reachable source sector. -/
theorem source_original_MEMORY_canonical_chain_exact434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (n start : ℕ) (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen) :
    memorySourceGEChain SP sm BP bm J ell m patterns cap q rho Vs V mu K
      zeta theta k N n start F y seen =
    sourceOriginalCanonicalGEChain434 SP sm BP bm J ell m cap patterns q rho Vs V mu K
      zeta theta k N n start F y seen := by
  induction n generalizing start y seen with
  | zero =>
      exact source_original_SOURCE_SYMMETRIC_G_canonical434 SP sm BP bm cap J ell
        hcap y seen hy q rho N start Vs V mu hVs hmu F
  | succ n ih =>
      simp only [memorySourceGEChain,sourceOriginalCanonicalGEChain434]
      symm
      rw [←source_original_SOURCE_SYMMETRIC_G_canonical434 SP sm BP bm cap J ell
        hcap y seen hy q rho N start Vs V mu hVs hmu]
      apply source_original_SYMMETRIC_G_reachable_congr434 SP sm BP bm cap J ell
        q rho N start Vs V mu y seen hy
      intro yg sg hg
      rw [←source_original_SOURCE_SYMMETRIC_E_canonical434 SP sm BP bm cap J ell m patterns
        hcap yg sg hg q rho Vs V mu hVs hmu]
      apply source_original_SYMMETRIC_E_reachable_congr434 SP sm BP bm cap J ell m patterns
        q rho Vs V mu _ zeta theta _ k yg sg hg
      intro ye se he
      exact (ih (start+1) ye se he).symm

def sourceOriginalCanonicalMemoryRoot434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ) : ℂ :=
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  (physicalSourceBaselineProduct BP bm q N : ℂ) *
    ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y : ℂ) *
      star (physicalVacuum SP sm BP bm J ell y) *
      (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then
        sourceOriginalCanonicalGEChain434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta k N N 0
          (fun out _ => physicalVacuum SP sm BP bm J ell out)
          y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
      else 0)

/-- Full original root, with its outer physical Fock orbit mass, baseline
and both vacuum factors, equals the chain of actual marked rows. -/
theorem source_original_MEMORY_root_canonical_exact434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hVs : ∀ g,0 < Vs g)
    (hmu : ∀ g p,0 < physicalSourceMuTilde BP bm q (2*R) V g p) :
    memorySourceRoot SP sm BP bm J ell m patterns cap q rho Vs V K zeta theta k R =
    sourceOriginalCanonicalMemoryRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R := by
  unfold memorySourceRoot sourceOriginalCanonicalMemoryRoot434
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hv : physicalVacuum SP sm BP bm J ell y=0
  · simp only [hv,star_zero,mul_zero,zero_mul]
  · by_cases hn : (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
    · simp only [if_pos hn]
      rw [source_original_MEMORY_canonical_chain_exact434
        SP sm BP bm J ell m cap patterns hcap q rho Vs V _ hVs hmu K zeta theta k (2*R)
        _ (2*R) 0 y _ (source_original_MEMORY_initial_reachable434
          SP sm BP bm J ell y hv hn)]
    · simp only [if_neg hn]

/-- Positivity of the exact source baseline follows from the original
prime-above-visits condition, with no analytic estimate assumed. -/
theorem source_original_SOURCE_baseline_positive434
    (q : ℝ) (hq : 0 ≤ q) (N : ℕ) (g : BG) (p : BP g)
    (hp : N+1 < bm g p) :
    0 < physicalSourceBaseline BP bm q N g p := by
  have hq0 (i : ℕ) : 0 ≤ sourceVisitQ q N i := by
    unfold sourceVisitQ
    split_ifs
    · exact Real.sqrt_nonneg _
    · exact hq
  have he (i : ℕ) : sourceVisitEta q N i ≤ 1 := by
    unfold sourceVisitEta
    linarith [hq0 i]
  have hs : (∑ i ∈ Finset.range (N+1),sourceVisitEta q N i) ≤ (N+1:ℕ) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range (N+1),(1:ℝ) := Finset.sum_le_sum (fun i _ => he i)
      _ = _ := by simp
  have hpn : (0:ℝ) < bm g p := by exact_mod_cast NeZero.pos (bm g p)
  unfold physicalSourceBaseline
  apply sub_pos.mpr
  apply (div_lt_one hpn).mpr
  exact hs.trans_lt (by exact_mod_cast hp)

theorem source_original_SOURCE_tilt_positive434
    (q : ℝ) (hq : 0 ≤ q) (N : ℕ) (V : BG → ℝ) (hV : ∀ g,0 < V g)
    (hp : ∀ g p,N+1 < bm g p) :
    ∀ g p,0 < physicalSourceMuTilde BP bm q N V g p := by
  intro g p
  unfold physicalSourceMuTilde
  exact one_div_pos.mpr (mul_pos
    (mul_pos (hV g) (by exact_mod_cast NeZero.pos (bm g p)))
    (source_original_SOURCE_baseline_positive434 BP bm q hq N g p (hp g p)))

/-- Applicable source-domain theorem: all normalization positivity is
discharged from the original physical domain, not supplied as a hidden
analytic or orbit-symmetry premise. -/
theorem source_original_MEMORY_root_canonical_source_domain434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP sm BP bm cap q rho Vs V k R) :
    memorySourceRoot SP sm BP bm J ell m patterns cap q rho Vs V K zeta theta k R =
    sourceOriginalCanonicalMemoryRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R :=
  source_original_MEMORY_root_canonical_exact434 SP sm BP bm J ell m cap patterns
    hd.cap_saturated q rho Vs V K zeta theta k R hd.Vsmall_pos
    (source_original_SOURCE_tilt_positive434 BP bm q hd.q_pos.le (2*R) V
      hd.Vbig_pos hd.big_above_visits)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPhysicalEPrelegalInventory -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Exactly the literal oriented E legality fields except for output
capacity. No arithmetic, residue or store/promotion condition is removed. -/
structure SourceOriginalOrientedBigPrelegal434
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p,NeZero (modulus p)] (M B : ℕ)
    (x : BigState modulus M B) (target : Fin M → P)
    (shared : Finset (Fin M)) (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ) (c : BigEdgeChoice modulus M B x) : Prop where
  shared_copy : ∀ j ∈ shared,x.1 (sigma j)=target (tau j)
  stores_unshared : c.1 ⊆ orientedUnshared M shared
  promotes_unshared : c.2.1 ⊆ orientedUnshared M shared
  promoted_matches : ∀ j : ↥c.2.1,target (tau j.val)=(x.2.2 (c.2.2 j)).1
  promoted_zero : ∀ j : ↥c.2.1,(x.2.2 (c.2.2 j)).2 +
    (step : ZMod (modulus (x.2.2 (c.2.2 j)).1))=0
  promoted_not_dividing : ∀ j : ↥c.2.1,¬modulus ((x.2.2 (c.2.2 j)).1) ∣ D
  stored_not_dividing : ∀ j ∈ c.1,¬modulus (x.1 (sigma j)) ∣ D

theorem source_original_ORIENTED_E_prelegal_capacity_iff434
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p,NeZero (modulus p)] (M B : ℕ)
    (x : BigState modulus M B) (target : Fin M → P)
    (shared : Finset (Fin M)) (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ) (c : BigEdgeChoice modulus M B x) :
    OrientedBigEdgeLegal modulus M B x target shared sigma tau D step c ↔
    SourceOriginalOrientedBigPrelegal434 modulus M B x target shared sigma tau D step c ∧
      (physicalPendingOutput modulus M B x sigma step c).length ≤ B := by
  constructor
  · intro h
    exact ⟨⟨h.shared_copy,h.stores_unshared,h.promotes_unshared,h.promoted_matches,
      h.promoted_zero,h.promoted_not_dividing,h.stored_not_dividing⟩,h.output_within_cutoff⟩
  · rintro ⟨h,hc⟩
    exact ⟨h.shared_copy,h.stores_unshared,h.promotes_unshared,h.promoted_matches,
      h.promoted_zero,h.promoted_not_dividing,h.stored_not_dividing,hc⟩

theorem source_original_PHYSICAL_E_prelegal_inventory_le434
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p,NeZero (modulus p)] (M B : ℕ)
    (x : BigState modulus M B) (target : Fin M → P)
    (shared : Finset (Fin M)) (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ) (c : BigEdgeChoice modulus M B x)
    (hc : SourceOriginalOrientedBigPrelegal434 modulus M B x target shared sigma tau D step c) :
    sourceOriginalBigInventory434 modulus M target
        (physicalPendingMultiset modulus M B x sigma step c) ≤
      sourceOriginalBigInventory434 modulus M x.1 (fockMultiset x.2) +
        ∑ j ∈ orientedFresh M shared c.2.1,
          ({modulus (target (tau j))} : Multiset ℕ) := by
  let a : Fin M → Multiset ℕ := fun j => {modulus (x.1 (sigma j))}
  let t : Fin M → Multiset ℕ := fun j => {modulus (target (tau j))}
  let o : Fin x.2.1.val → Multiset ℕ := fun j => {modulus (x.2.2 j).1}
  have hpart :
      (∑ j ∈ orientedFresh M shared c.2.1,t j) +
        (∑ j ∈ c.2.1,t j) + (∑ j ∈ shared,t j) = ∑ j,t j := by
    rw [orientedFresh,Finset.sum_sdiff hc.promotes_unshared]
    exact Finset.sum_sdiff (Finset.subset_univ shared)
  have hprom : (∑ j ∈ c.2.1,t j) = ∑ j ∈ selectedOld modulus M B x c,o j := by
    rw [selectedOld,Finset.sum_image (fun i hi j hj h => c.2.2.injective h)]
    rw [←Finset.sum_attach c.2.1]
    change (∑ j : ↥c.2.1,t j.val) = ∑ j : ↥c.2.1,o (c.2.2 j)
    apply Finset.sum_congr rfl
    intro j hj
    simp only [t,o,hc.promoted_matches j]
  have hshared : (∑ j ∈ shared,t j) = ∑ j ∈ shared,a j := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [t,a,←hc.shared_copy j hj]
  have hold : (fockMultiset x.2).map (fun z => modulus z.1) = ∑ j,o j := by
    unfold fockMultiset
    rw [Multiset.map_coe,List.map_ofFn,source_original_inventory_ofFn_bag434]
    rfl
  have hpend :
      (physicalPendingMultiset modulus M B x sigma step c).map
          (fun z => modulus z.1) =
        (∑ j ∈ survivorIndices modulus M B x c,o j) +
        (∑ j ∈ c.1,a j) := by
    simp only [physicalPendingMultiset,physicalPendingOutput,←Multiset.coe_add,
      Multiset.map_add,survivors,newlyStored,Multiset.map_coe,List.map_map,
      Function.comp_def,translateAtom]
    rw [source_original_inventory_indexed_bag434,source_original_inventory_indexed_bag434]
  have hsurv : (∑ j ∈ survivorIndices modulus M B x c,o j) +
      (∑ j ∈ selectedOld modulus M B x c,o j) = ∑ j,o j :=
    Finset.sum_sdiff (Finset.subset_univ _)
  have hd : Disjoint shared c.1 := by
    apply Finset.disjoint_left.mpr
    intro j hj hjc
    exact (Finset.mem_sdiff.mp (hc.stores_unshared hjc)).2 hj
  have ha : (∑ j ∈ shared,a j) + (∑ j ∈ c.1,a j) ≤ ∑ j,a j := by
    rw [←Finset.sum_union hd]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hta : (∑ j : Fin M,({modulus (target j)}:Multiset ℕ)) = ∑ j,t j :=
    (Equiv.sum_comp tau (fun j => ({modulus (target j)}:Multiset ℕ))).symm
  have haa : (∑ j : Fin M,({modulus (x.1 j)}:Multiset ℕ)) = ∑ j,a j :=
    (Equiv.sum_comp sigma (fun j => ({modulus (x.1 j)}:Multiset ℕ))).symm
  unfold sourceOriginalBigInventory434
  rw [hpend,hold,hta,haa,←hpart,hprom,hshared]
  calc
    _ = ((∑ j ∈ shared,a j)+(∑ j ∈ c.1,a j)) +
          ((∑ j ∈ survivorIndices modulus M B x c,o j)+
           (∑ j ∈ selectedOld modulus M B x c,o j)) +
          (∑ j ∈ orientedFresh M shared c.2.1,t j) := by ac_rfl
    _ ≤ (∑ j,a j) + (∑ j,o j) +
          (∑ j ∈ orientedFresh M shared c.2.1,t j) := by
      rw [hsurv]
      exact add_le_add (add_le_add ha le_rfl) le_rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPhysicalGhostAtom -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64MemoryGhostOp
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ) (cap : BG → ℕ)

abbrev SourceOriginalPhysicalGhostAtomWitness434
    (y : FullPhysicalOutput SP sm BP bm M) :=
  (g : BG) →
    {A : Finset (Atom (BP g) (bm g)) //
      A ∈ ((y.2 g).2.toFinset.filter (fun z => z.2=0)).powerset} ×
    Finset (Atom (BP g) (bm g))

def sourceOriginalPhysicalGhostAtomBirths434
    (y : FullPhysicalOutput SP sm BP bm M)
    (d : SourceOriginalPhysicalGhostAtomWitness434 SP sm BP bm M y) : List ℕ :=
  (Finset.univ : Finset BG).toList.flatMap (fun g =>
    (d g).2.toList.map (fun z => bm g z.1))

def sourceOriginalPhysicalGhostAtomEligible434
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (d : SourceOriginalPhysicalGhostAtomWitness434 SP sm BP bm M y) : Prop :=
  (sourceOriginalPhysicalGhostAtomBirths434 SP sm BP bm M y d).Nodup ∧
    Disjoint seen (sourceOriginalPhysicalGhostAtomBirths434 SP sm BP bm M y d).toFinset

def sourceOriginalPhysicalGhostAtomOutput434
    (y : FullPhysicalOutput SP sm BP bm M)
    (d : SourceOriginalPhysicalGhostAtomWitness434 SP sm BP bm M y) :
    FullPhysicalOutput SP sm BP bm M :=
  (y.1,fun g => ((y.2 g).1,
    (∑ z ∈ (y.2 g).2.toFinset \ (d g).1.1,({z}:Multiset (Atom (BP g) (bm g)))) +
      ∑ z ∈ (d g).2,({z}:Multiset (Atom (BP g) (bm g)))))

def sourceOriginalPhysicalGhostAtomCoefficient434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP sm BP bm M)
    (d : SourceOriginalPhysicalGhostAtomWitness434 SP sm BP bm M y) : ℂ :=
  ∏ g,
    (-((sourceVisitEta q N i:ℝ):ℂ)/(rho:ℂ))^(d g).1.1.card *
    (((sourceVisitQ q N i:ℝ):ℂ)/(rho:ℂ)^2)^
      (((y.2 g).2.toFinset.filter (fun z => z.2=0)).card-(d g).1.1.card) *
    (-((sourceVisitEta q N i:ℝ):ℂ)*(V g:ℂ)/(rho:ℂ))^(d g).2.card *
    (∏ z ∈ (d g).2,sourceBirthNu (fun p => (mu g p:ℂ)) z)

/-- Atom-subset form of the original all-group G row. There are no OLD
indices or cap tests; the single original numeric birth gate and the
arbitrary joint terminal function remain inside the sum. -/
def sourceOriginalPhysicalGhostAtomRow434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ) : ℂ :=
  ∑ d : SourceOriginalPhysicalGhostAtomWitness434 SP sm BP bm M y,
    if sourceOriginalPhysicalGhostAtomEligible434 SP sm BP bm M y seen d then
      sourceOriginalPhysicalGhostAtomCoefficient434 SP sm BP bm M q rho N i V mu y d *
        F (sourceOriginalPhysicalGhostAtomOutput434 SP sm BP bm M y d)
          (seen ∪ (sourceOriginalPhysicalGhostAtomBirths434 SP sm BP bm M y d).toFinset)
    else 0

def sourceOriginalPhysicalGhostAtomEquiv434
    (x : FullPhysicalState SP sm BP bm M cap)
    (hn : ∀ g,(fockToList (x.2 g).2).Nodup) :
    SourceOriginalPhysicalGhostSetWitness434 SP sm BP bm M cap x ≃
      SourceOriginalPhysicalGhostAtomWitness434 SP sm BP bm M
        (physicalFockProjection SP sm BP bm M cap x) :=
  Equiv.piCongrRight (fun g => sourceOriginalGhostAtomEquiv434
    (fockToList (x.2 g).2) (fun z : Atom (BP g) (bm g) => z.2=0) (hn g))

theorem source_original_PHYSICAL_G_atom_births434
    (x : FullPhysicalState SP sm BP bm M cap)
    (hn : ∀ g,(fockToList (x.2 g).2).Nodup)
    (d : SourceOriginalPhysicalGhostSetWitness434 SP sm BP bm M cap x) :
    sourceOriginalPhysicalGhostAtomBirths434 SP sm BP bm M
      (physicalFockProjection SP sm BP bm M cap x)
      (sourceOriginalPhysicalGhostAtomEquiv434 SP sm BP bm M cap x hn d) =
    sourceOriginalPhysicalGhostSetBirths434 SP sm BP bm M cap x d := rfl

theorem source_original_PHYSICAL_G_atom_output434
    (x : FullPhysicalState SP sm BP bm M cap)
    (hn : ∀ g,(fockToList (x.2 g).2).Nodup)
    (d : SourceOriginalPhysicalGhostSetWitness434 SP sm BP bm M cap x) :
    sourceOriginalPhysicalGhostAtomOutput434 SP sm BP bm M
      (physicalFockProjection SP sm BP bm M cap x)
      (sourceOriginalPhysicalGhostAtomEquiv434 SP sm BP bm M cap x hn d) =
    sourceOriginalPhysicalGhostSetOutput434 SP sm BP bm M cap x d := by
  apply Prod.ext
  · rfl
  · funext g
    apply Prod.ext
    · rfl
    · change (∑ z ∈ (fockToList (x.2 g).2).toFinset \
          (d g).1.1.map (sourceOriginalOldGetEmbedding434 (fockToList (x.2 g).2) (hn g)),
          ({z}:Multiset (Atom (BP g) (bm g)))) +
          (∑ z ∈ (d g).2,({z}:Multiset (Atom (BP g) (bm g)))) =
        memoryTupleBag (fun j : {j : Fin (fockToList (x.2 g).2).length // j ∉ (d g).1.1} =>
          (fockToList (x.2 g).2).get j) +
          (∑ z ∈ (d g).2,({z}:Multiset (Atom (BP g) (bm g))))
      rw [source_original_G_old_atom_survivors434]

theorem source_original_PHYSICAL_G_atom_coefficient434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP sm BP bm M cap)
    (hn : ∀ g,(fockToList (x.2 g).2).Nodup)
    (d : SourceOriginalPhysicalGhostSetWitness434 SP sm BP bm M cap x) :
    sourceOriginalPhysicalGhostAtomCoefficient434 SP sm BP bm M q rho N i V mu
      (physicalFockProjection SP sm BP bm M cap x)
      (sourceOriginalPhysicalGhostAtomEquiv434 SP sm BP bm M cap x hn d) =
    sourceOriginalPhysicalGhostSetUncutCoefficient434 SP sm BP bm M cap q rho N i V mu x d := by
  unfold sourceOriginalPhysicalGhostAtomCoefficient434 sourceOriginalPhysicalGhostSetUncutCoefficient434
  apply Finset.prod_congr rfl
  intro g hg
  change
    (-((sourceVisitEta q N i:ℝ):ℂ)/(rho:ℂ))^
      ((sourceOriginalGhostOldAtomEquiv434 (fockToList (x.2 g).2)
        (fun z => z.2=0) (hn g) (d g).1).1).card *
    (((sourceVisitQ q N i:ℝ):ℂ)/(rho:ℂ)^2)^
      (((fockToList (x.2 g).2).toFinset.filter (fun z => z.2=0)).card-
        ((sourceOriginalGhostOldAtomEquiv434 (fockToList (x.2 g).2)
          (fun z => z.2=0) (hn g) (d g).1).1).card) *
    (-((sourceVisitEta q N i:ℝ):ℂ)*(V g:ℂ)/(rho:ℂ))^(d g).2.card *
    (∏ z ∈ (d g).2,sourceBirthNu (fun p => (mu g p:ℂ)) z) = _
  rw [source_original_G_old_atom_card434,
    source_original_G_zero_atom_card434 (fockToList (x.2 g).2) (fun z => z.2=0) (hn g)]

/-- Exact original marked G on its proved reachable sector. The OLD
positional sum has now been removed by a genuine bijection. -/
theorem source_original_PHYSICAL_MARKED_G_atom_row434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP sm BP bm M cap) (seen : Finset ℕ)
    (hx : sourceOriginalPhysicalReachable434 SP sm BP bm M
      (physicalFockProjection SP sm BP bm M cap x) seen)
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ) :
    physicalGBirthMarkedRow SP sm BP bm M cap q rho N i V mu x seen F =
    sourceOriginalPhysicalGhostAtomRow434 SP sm BP bm M q rho N i V mu
      (physicalFockProjection SP sm BP bm M cap x) seen F := by
  obtain ⟨ho,hs⟩ := source_original_PHYSICAL_reachable_pending434 SP sm BP bm M cap x seen hx
  let hn : ∀ g,(fockToList (x.2 g).2).Nodup := fun g => (ho g).of_map (fun z => z.1)
  rw [source_original_PHYSICAL_MARKED_G_saturated_set_extraction434
    SP sm BP bm M cap q rho N i V mu x seen ho hs hcap F]
  unfold sourceOriginalPhysicalGhostAtomRow434
  apply Fintype.sum_equiv (sourceOriginalPhysicalGhostAtomEquiv434 SP sm BP bm M cap x hn)
  intro d
  unfold sourceOriginalPhysicalGhostAtomEligible434 sourceOriginalPhysicalGhostSetEligible434
  rw [source_original_PHYSICAL_G_atom_births434,
    source_original_PHYSICAL_G_atom_output434,source_original_PHYSICAL_G_atom_coefficient434]

theorem source_original_PHYSICAL_SYMMETRIC_G_atom_row434
    (J ell : ℕ) (q rho : ℝ) (N i : ℕ)
    (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen)
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    physicalMarkedSymmetricG SP sm BP bm J ell cap q rho N i Vs V mu y seen F =
    sourceOriginalPhysicalGhostAtomRow434 SP sm BP bm (J+ell) q rho N i V mu y seen F := by
  have hp := source_original_REACHABLE_canonical_projection434
    SP sm BP bm (J+ell) cap hcap y seen hy
  rw [source_original_SOURCE_SYMMETRIC_G_canonical434
    SP sm BP bm cap J ell hcap y seen hy q rho N i Vs V mu hVs hmu]
  have hh := source_original_PHYSICAL_MARKED_G_atom_row434
    SP sm BP bm (J+ell) cap q rho N i V mu
    (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap y) seen
    (by simpa only [hp] using hy) hcap F
  simpa only [hp] using hh
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryAtomChain -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Exact G atom-subset rows followed by literal source E rows on canonical
OLD representatives. Every global birth gate and common continuation
is preserved, with no internal orbit average or G OLD-position index. -/
def sourceOriginalAtomGEChain434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ) :
    (remaining start : ℕ) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
  | 0,start,F => fun y seen =>
      sourceOriginalPhysicalGhostAtomRow434 SP sm BP bm (J+ell) q rho N start V mu
        y seen F
  | n+1,start,F => fun y seen =>
      sourceOriginalPhysicalGhostAtomRow434 SP sm BP bm (J+ell) q rho N start V mu
        y seen
        (fun yg sg =>
          physicalOrientedBirthMarkedE SP sm BP bm J ell m cap patterns
            q rho Vs V mu
            (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
            zeta theta (physicalAlternatingSign start) k
            (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg
            (sourceOriginalAtomGEChain434 q rho Vs V mu K zeta theta k N n (start+1) F))

/-- Exact chain descent, uniform in all finite carriers, depths and joint
terminal tests. Only physical positivity and the original saturated caps
are needed in addition to the proved reachable source sector. -/
theorem source_original_MEMORY_atom_chain_exact434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (n start : ℕ) (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen) :
    memorySourceGEChain SP sm BP bm J ell m patterns cap q rho Vs V mu K
      zeta theta k N n start F y seen =
    sourceOriginalAtomGEChain434 SP sm BP bm J ell m cap patterns q rho Vs V mu K
      zeta theta k N n start F y seen := by
  induction n generalizing start y seen with
  | zero =>
      exact source_original_PHYSICAL_SYMMETRIC_G_atom_row434 SP sm BP bm cap J ell
        q rho N start Vs V mu hVs hmu y seen hy hcap F
  | succ n ih =>
      simp only [memorySourceGEChain,sourceOriginalAtomGEChain434]
      symm
      rw [←source_original_PHYSICAL_SYMMETRIC_G_atom_row434 SP sm BP bm cap J ell
        q rho N start Vs V mu hVs hmu y seen hy hcap]
      apply source_original_SYMMETRIC_G_reachable_congr434 SP sm BP bm cap J ell
        q rho N start Vs V mu y seen hy
      intro yg sg hg
      rw [←source_original_SOURCE_SYMMETRIC_E_canonical434 SP sm BP bm cap J ell m patterns
        hcap yg sg hg q rho Vs V mu hVs hmu]
      apply source_original_SYMMETRIC_E_reachable_congr434 SP sm BP bm cap J ell m patterns
        q rho Vs V mu _ zeta theta _ k yg sg hg
      intro ye se he
      exact (ih (start+1) ye se he).symm

def sourceOriginalAtomMemoryRoot434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ) : ℂ :=
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  (physicalSourceBaselineProduct BP bm q N : ℂ) *
    ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y : ℂ) *
      star (physicalVacuum SP sm BP bm J ell y) *
      (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then
        sourceOriginalAtomGEChain434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta k N N 0
          (fun out _ => physicalVacuum SP sm BP bm J ell out)
          y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
      else 0)

/-- Full original root, with its outer physical Fock orbit mass, baseline
and both vacuum factors, equals the chain of actual marked rows. -/
theorem source_original_MEMORY_root_atom_exact434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hVs : ∀ g,0 < Vs g)
    (hmu : ∀ g p,0 < physicalSourceMuTilde BP bm q (2*R) V g p) :
    memorySourceRoot SP sm BP bm J ell m patterns cap q rho Vs V K zeta theta k R =
    sourceOriginalAtomMemoryRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R := by
  unfold memorySourceRoot sourceOriginalAtomMemoryRoot434
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hv : physicalVacuum SP sm BP bm J ell y=0
  · simp only [hv,star_zero,mul_zero,zero_mul]
  · by_cases hn : (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
    · simp only [if_pos hn]
      rw [source_original_MEMORY_atom_chain_exact434
        SP sm BP bm J ell m cap patterns hcap q rho Vs V _ hVs hmu K zeta theta k (2*R)
        _ (2*R) 0 y _ (source_original_MEMORY_initial_reachable434
          SP sm BP bm J ell y hv hn)]
    · simp only [if_neg hn]

/-- Applicable original finite root with actual atom-subset G, original
source E, fixed phases and both vacuum/Fock endpoints. -/
theorem source_original_MEMORY_root_atom_source_domain434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP sm BP bm cap q rho Vs V k R) :
    memorySourceRoot SP sm BP bm J ell m patterns cap q rho Vs V K zeta theta k R =
    sourceOriginalAtomMemoryRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R :=
  source_original_MEMORY_root_atom_exact434 SP sm BP bm J ell m cap patterns
    hd.cap_saturated q rho Vs V K zeta theta k R hd.Vsmall_pos
    (source_original_SOURCE_tilt_positive434 BP bm q hd.q_pos.le (2*R) V
      hd.Vbig_pos hd.big_above_visits)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalGhostZeroBirthSubsets -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Exact finite subset support transport for an arbitrary joint test. -/
theorem source_original_subset_supported_embedding434
    {P U : Type} [Fintype P] [DecidableEq P] [Fintype U] [DecidableEq U]
    (f : P ↪ U) (w : U → ℂ)
    (hw : ∀ u,u ∉ (Finset.univ : Finset P).map f → w u=0)
    (gamma : ℂ) (H : Finset U → ℂ) :
    (∑ B : Finset U,gamma^B.card*(∏ u ∈ B,w u)*H B) =
    ∑ A : Finset P,gamma^A.card*(∏ p ∈ A,w (f p))*H (A.map f) := by
  let s := (Finset.univ : Finset P).map f
  have hr : (∑ B : Finset U,gamma^B.card*(∏ u ∈ B,w u)*H B) =
      ∑ B ∈ s.powerset,gamma^B.card*(∏ u ∈ B,w u)*H B := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro B hB hnot
    have hn : ¬ B ⊆ s := by simpa only [Finset.mem_powerset] using hnot
    change ¬∀ u,u ∈ B → u ∈ s at hn
    push Not at hn
    obtain ⟨u,hu,hus⟩ := hn
    rw [Finset.prod_eq_zero hu (hw u hus),mul_zero,zero_mul]
  rw [hr]
  symm
  apply Finset.sum_bij (fun A _ => A.map f)
  · intro A hA
    apply Finset.mem_powerset.mpr
    intro u hu
    obtain ⟨p,hp,hpu⟩ := Finset.mem_map.mp hu
    exact Finset.mem_map.mpr ⟨p,Finset.mem_univ _,hpu⟩
  · intro A hA B hB hAB
    apply Finset.ext
    intro p
    have hh := congrArg (fun S : Finset U => f p ∈ S) hAB
    simpa only [Finset.mem_map,EmbeddingLike.apply_eq_iff_eq,exists_eq_right] using Iff.of_eq hh
  · intro B hB
    let e := sourceOriginalSubsetEmbeddingEquiv434 (Finset.univ : Finset P) f
    let A := e.symm ⟨B,hB⟩
    refine ⟨A.1,Finset.mem_univ _,?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply ⟨B,hB⟩)
  · intro A hA
    simp only [Finset.card_map,Finset.prod_map]

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]

def sourceOriginalZeroAtomEmbedding434 : P ↪ Atom P modulus :=
  ⟨zeroAtom,fun _ _ h => congrArg Sigma.fst h⟩

theorem source_original_ZERO_BIRTH_support434
    (mu : P → ℂ) (z : Atom P modulus)
    (hz : z ∉ (Finset.univ : Finset P).map (sourceOriginalZeroAtomEmbedding434 modulus)) :
    sourceBirthNu mu z=0 := by
  rcases z with ⟨p,r⟩
  by_cases hr : r=0
  · subst r
    exact False.elim (hz (Finset.mem_map.mpr ⟨p,Finset.mem_univ _,rfl⟩))
  · exact birthMass_nonzero_residue mu ⟨p,r⟩ hr

/-- The actual source birth law removes every nonzero-residue fresh
subset. No change to the arbitrary terminal test is assumed. -/
theorem source_original_ZERO_BIRTH_subset_sum434
    (mu : P → ℂ) (gamma : ℂ) (H : Finset (Atom P modulus) → ℂ) :
    (∑ B : Finset (Atom P modulus),
      gamma^B.card*(∏ z ∈ B,sourceBirthNu mu z)*H B) =
    ∑ B : Finset P,gamma^B.card*(∏ p ∈ B,mu p)*
      H (B.map (sourceOriginalZeroAtomEmbedding434 modulus)) := by
  have hh := source_original_subset_supported_embedding434
    (sourceOriginalZeroAtomEmbedding434 modulus) (sourceBirthNu mu)
    (source_original_ZERO_BIRTH_support434 modulus mu) gamma H
  have hz (p : P) : sourceBirthNu mu (sourceOriginalZeroAtomEmbedding434 modulus p)=mu p := by
    change birthMass mu (zeroAtom p : Atom P modulus)=mu p
    exact birthMass_zero mu p
  simpa only [hz] using hh
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalGhostPrimeBirthRow -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

section OneGroup
variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]
variable (S : Finset (Atom P modulus))

abbrev SourceOriginalGroupPrimeBirthChoice434 :=
  {A : Finset (Atom P modulus) // A ∈ S.powerset} × Finset P

def sourceOriginalGroupPrimeBirthLift434
    (d : SourceOriginalGroupPrimeBirthChoice434 modulus S) :
    {A : Finset (Atom P modulus) // A ∈ S.powerset} × Finset (Atom P modulus) :=
  (d.1,d.2.map (sourceOriginalZeroAtomEmbedding434 modulus))

def sourceOriginalGroupPrimeBirthWeight434 (alpha chi gamma : ℂ) (mu : P → ℂ)
    (d : SourceOriginalGroupPrimeBirthChoice434 modulus S) : ℂ :=
  alpha^d.1.1.card * chi^(S.card-d.1.1.card) *
    gamma^d.2.card * (∏ p ∈ d.2,mu p)

theorem source_original_GROUP_G_prime_birth_sum434
    (alpha chi gamma : ℂ) (mu : P → ℂ)
    (H : ({A : Finset (Atom P modulus) // A ∈ S.powerset} ×
      Finset (Atom P modulus)) → ℂ) :
    (∑ d : SourceOriginalGroupPrimeBirthChoice434 modulus S,
      sourceOriginalGroupPrimeBirthWeight434 modulus S alpha chi gamma mu d *
        H (sourceOriginalGroupPrimeBirthLift434 modulus S d)) =
    ∑ d : ({A : Finset (Atom P modulus) // A ∈ S.powerset} × Finset (Atom P modulus)),
      (alpha^d.1.1.card * chi^(S.card-d.1.1.card) *
        gamma^d.2.card * (∏ z ∈ d.2,sourceBirthNu mu z)) * H d := by
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro A hA
  have hh := source_original_ZERO_BIRTH_subset_sum434 modulus mu gamma (fun B => H (A,B))
  have hh' := congrArg (fun t : ℂ => (alpha^A.1.card*chi^(S.card-A.1.card))*t) hh
  simpa only [sourceOriginalGroupPrimeBirthWeight434,sourceOriginalGroupPrimeBirthLift434,
    Finset.mul_sum,mul_assoc] using hh'.symm
end OneGroup

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ)

abbrev SourceOriginalPhysicalGhostPrimeBirthWitness434
    (y : FullPhysicalOutput SP sm BP bm M) :=
  (g : BG) → SourceOriginalGroupPrimeBirthChoice434 (bm g)
    ((y.2 g).2.toFinset.filter (fun z => z.2=0))

def sourceOriginalPhysicalGhostPrimeBirthLift434
    (y : FullPhysicalOutput SP sm BP bm M)
    (d : SourceOriginalPhysicalGhostPrimeBirthWitness434 SP sm BP bm M y) :
    SourceOriginalPhysicalGhostAtomWitness434 SP sm BP bm M y :=
  fun g => sourceOriginalGroupPrimeBirthLift434 (bm g) _ (d g)

def sourceOriginalPhysicalGhostPrimeBirthCoefficient434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP sm BP bm M)
    (d : SourceOriginalPhysicalGhostPrimeBirthWitness434 SP sm BP bm M y) : ℂ :=
  ∏ g,sourceOriginalGroupPrimeBirthWeight434 (bm g) _
    (-((sourceVisitEta q N i:ℝ):ℂ)/(rho:ℂ))
    (((sourceVisitQ q N i:ℝ):ℂ)/(rho:ℂ)^2)
    (-((sourceVisitEta q N i:ℝ):ℂ)*(V g:ℂ)/(rho:ℂ))
    (fun p => (mu g p:ℂ)) (d g)

/-- Exact source births indexed by prime-label subsets, with every new
residue fixed to zero by the original sourceBirthNu support. The global
numerical birth gate and the arbitrary joint F are still literal. -/
def sourceOriginalPhysicalGhostPrimeBirthRow434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ) : ℂ :=
  ∑ d : SourceOriginalPhysicalGhostPrimeBirthWitness434 SP sm BP bm M y,
    let e := sourceOriginalPhysicalGhostPrimeBirthLift434 SP sm BP bm M y d
    if sourceOriginalPhysicalGhostAtomEligible434 SP sm BP bm M y seen e then
      sourceOriginalPhysicalGhostPrimeBirthCoefficient434 SP sm BP bm M q rho N i V mu y d *
        F (sourceOriginalPhysicalGhostAtomOutput434 SP sm BP bm M y e)
          (seen ∪ (sourceOriginalPhysicalGhostAtomBirths434 SP sm BP bm M y e).toFinset)
    else 0

/-- Exact physical atom G equals the prime-birth subset row, for all
joint terminal tests and all finite groups. This is an applied support
calculation, with no norm or independence premise. -/
theorem source_original_PHYSICAL_G_atom_prime_birth_row434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ) :
    sourceOriginalPhysicalGhostAtomRow434 SP sm BP bm M q rho N i V mu y seen F =
    sourceOriginalPhysicalGhostPrimeBirthRow434 SP sm BP bm M q rho N i V mu y seen F := by
  let H : SourceOriginalPhysicalGhostAtomWitness434 SP sm BP bm M y → ℂ := fun d =>
    if sourceOriginalPhysicalGhostAtomEligible434 SP sm BP bm M y seen d then
      F (sourceOriginalPhysicalGhostAtomOutput434 SP sm BP bm M y d)
        (seen ∪ (sourceOriginalPhysicalGhostAtomBirths434 SP sm BP bm M y d).toFinset)
    else 0
  have hh := source_original_GHOST_joint_exact_transfer434
    (fun g => SourceOriginalGroupPrimeBirthChoice434 (bm g)
      ((y.2 g).2.toFinset.filter (fun z => z.2=0)))
    (fun g => {A : Finset (Atom (BP g) (bm g)) //
      A ∈ ((y.2 g).2.toFinset.filter (fun z => z.2=0)).powerset} × Finset (Atom (BP g) (bm g)))
    (fun g => sourceOriginalGroupPrimeBirthLift434 (bm g) _)
    (fun g => sourceOriginalGroupPrimeBirthWeight434 (bm g) _
      (-((sourceVisitEta q N i:ℝ):ℂ)/(rho:ℂ))
      (((sourceVisitQ q N i:ℝ):ℂ)/(rho:ℂ)^2)
      (-((sourceVisitEta q N i:ℝ):ℂ)*(V g:ℂ)/(rho:ℂ))
      (fun p => (mu g p:ℂ)))
    (fun g d =>
      (-((sourceVisitEta q N i:ℝ):ℂ)/(rho:ℂ))^d.1.1.card *
      (((sourceVisitQ q N i:ℝ):ℂ)/(rho:ℂ)^2)^
        (((y.2 g).2.toFinset.filter (fun z => z.2=0)).card-d.1.1.card) *
      (-((sourceVisitEta q N i:ℝ):ℂ)*(V g:ℂ)/(rho:ℂ))^d.2.card *
      (∏ z ∈ d.2,sourceBirthNu (fun p => (mu g p:ℂ)) z))
    (fun g H => source_original_GROUP_G_prime_birth_sum434 (bm g) _ _ _ _ _ H) H
  unfold sourceOriginalPhysicalGhostAtomRow434 sourceOriginalPhysicalGhostPrimeBirthRow434
    sourceOriginalPhysicalGhostAtomCoefficient434 sourceOriginalPhysicalGhostPrimeBirthCoefficient434
  simp only [H,mul_ite,mul_zero] at hh
  convert hh.symm using 1 <;> try rfl

theorem source_original_PHYSICAL_MARKED_G_prime_birth_row434
    (cap : BG → ℕ) (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP sm BP bm M cap) (seen : Finset ℕ)
    (hx : sourceOriginalPhysicalReachable434 SP sm BP bm M
      (physicalFockProjection SP sm BP bm M cap x) seen)
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ) :
    physicalGBirthMarkedRow SP sm BP bm M cap q rho N i V mu x seen F =
    sourceOriginalPhysicalGhostPrimeBirthRow434 SP sm BP bm M q rho N i V mu
      (physicalFockProjection SP sm BP bm M cap x) seen F := by
  rw [source_original_PHYSICAL_MARKED_G_atom_row434
    SP sm BP bm M cap q rho N i V mu x seen hx hcap F,
    source_original_PHYSICAL_G_atom_prime_birth_row434]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalGhostPrimeBirthGate -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

theorem source_original_ZERO_BIRTH_numeric_list_perm434
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p,NeZero (modulus p)] (value : P → ℕ) (s : Finset P) :
    ((s.map (sourceOriginalZeroAtomEmbedding434 modulus)).toList.map
      (fun z => value z.1)).Perm (s.toList.map value) := by
  apply Multiset.coe_eq_coe.mp
  simp only [←Multiset.map_coe,Finset.coe_toList]
  change (s.val.map (sourceOriginalZeroAtomEmbedding434 modulus)).map
    (fun z => value z.1)=s.val.map value
  rw [Multiset.map_map]
  rfl

/-- Distinct prime-label subsets across the original globally injective
prime families have a globally Nodup numerical birth list. -/
theorem source_original_FAMILY_subset_numeric_nodup434
    {I : Type} [Fintype I] [DecidableEq I]
    (P : I → Type) [∀ i,Fintype (P i)] [∀ i,DecidableEq (P i)]
    (value : (i : I) → P i → ℕ)
    (hi : Function.Injective (fun x : Sigma P => value x.1 x.2))
    (s : (i : I) → Finset (P i)) :
    ((Finset.univ : Finset I).toList.flatMap (fun i => (s i).toList.map (value i))).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro i hi'
    apply List.Nodup.map _ (Finset.nodup_toList _)
    intro p q hpq
    have hh : (⟨i,p⟩ : Sigma P)=⟨i,q⟩ := hi hpq
    exact eq_of_heq (Sigma.mk.inj_iff.mp hh).2
  · apply List.Pairwise.imp _ (Finset.nodup_toList (Finset.univ : Finset I))
    intro i j hij
    apply List.disjoint_left.mpr
    intro n hn hm
    obtain ⟨p,hp,hpn⟩ := List.mem_map.mp hn
    obtain ⟨q,hq,hqn⟩ := List.mem_map.mp hm
    have he : (⟨i,p⟩ : Sigma P)=⟨j,q⟩ := hi (hpn.trans hqn.symm)
    exact hij (congrArg Sigma.fst he)

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ)

def sourceOriginalPhysicalGhostPrimeBirthNumbers434
    (y : FullPhysicalOutput SP sm BP bm M)
    (d : SourceOriginalPhysicalGhostPrimeBirthWitness434 SP sm BP bm M y) : List ℕ :=
  (Finset.univ : Finset BG).toList.flatMap (fun g => (d g).2.toList.map (bm g))

def sourceOriginalPhysicalGhostPrimeBirthSet434
    (y : FullPhysicalOutput SP sm BP bm M)
    (d : SourceOriginalPhysicalGhostPrimeBirthWitness434 SP sm BP bm M y) : Finset ℕ :=
  Finset.univ.biUnion (fun g => (d g).2.image (bm g))

theorem source_original_PHYSICAL_G_prime_birth_numbers434
    (y : FullPhysicalOutput SP sm BP bm M)
    (d : SourceOriginalPhysicalGhostPrimeBirthWitness434 SP sm BP bm M y) :
    (sourceOriginalPhysicalGhostAtomBirths434 SP sm BP bm M y
      (sourceOriginalPhysicalGhostPrimeBirthLift434 SP sm BP bm M y d)).Perm
    (sourceOriginalPhysicalGhostPrimeBirthNumbers434 SP sm BP bm M y d) := by
  unfold sourceOriginalPhysicalGhostAtomBirths434 sourceOriginalPhysicalGhostPrimeBirthLift434
    sourceOriginalPhysicalGhostPrimeBirthNumbers434
  apply List.Perm.flatMap (List.Perm.refl _)
  intro g hg
  exact source_original_ZERO_BIRTH_numeric_list_perm434 (bm g) (bm g) (d g).2

theorem source_original_PHYSICAL_G_prime_birth_set434
    (y : FullPhysicalOutput SP sm BP bm M)
    (d : SourceOriginalPhysicalGhostPrimeBirthWitness434 SP sm BP bm M y) :
    (sourceOriginalPhysicalGhostAtomBirths434 SP sm BP bm M y
      (sourceOriginalPhysicalGhostPrimeBirthLift434 SP sm BP bm M y d)).toFinset =
    sourceOriginalPhysicalGhostPrimeBirthSet434 SP sm BP bm M y d := by
  ext n
  rw [List.mem_toFinset,
    (source_original_PHYSICAL_G_prime_birth_numbers434 SP sm BP bm M y d).mem_iff]
  simp [sourceOriginalPhysicalGhostPrimeBirthNumbers434,sourceOriginalPhysicalGhostPrimeBirthSet434]

theorem source_original_PHYSICAL_G_prime_birth_nodup434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (y : FullPhysicalOutput SP sm BP bm M)
    (d : SourceOriginalPhysicalGhostPrimeBirthWitness434 SP sm BP bm M y) :
    (sourceOriginalPhysicalGhostAtomBirths434 SP sm BP bm M y
      (sourceOriginalPhysicalGhostPrimeBirthLift434 SP sm BP bm M y d)).Nodup := by
  apply (source_original_PHYSICAL_G_prime_birth_numbers434 SP sm BP bm M y d).nodup_iff.mpr
  exact source_original_FAMILY_subset_numeric_nodup434 BP bm hi (fun g => (d g).2)

/-- The actual global numerical birth gate is exactly the no-rebirth
condition for each selected prime. Global source injectivity is explicit. -/
theorem source_original_PHYSICAL_G_prime_birth_gate434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (d : SourceOriginalPhysicalGhostPrimeBirthWitness434 SP sm BP bm M y) :
    sourceOriginalPhysicalGhostAtomEligible434 SP sm BP bm M y seen
      (sourceOriginalPhysicalGhostPrimeBirthLift434 SP sm BP bm M y d) ↔
    ∀ g,∀ p ∈ (d g).2,bm g p ∉ seen := by
  unfold sourceOriginalPhysicalGhostAtomEligible434
  rw [source_original_PHYSICAL_G_prime_birth_set434]
  constructor
  · rintro ⟨_,hd⟩ g p hp hseen
    apply Finset.disjoint_left.mp hd hseen
    exact Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ _,Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩
  · intro h
    refine ⟨source_original_PHYSICAL_G_prime_birth_nodup434 SP sm BP bm M hi y d,?_⟩
    apply Finset.disjoint_left.mpr
    intro n hn hb
    obtain ⟨g,hg,hb'⟩ := Finset.mem_biUnion.mp hb
    obtain ⟨p,hp,hpn⟩ := Finset.mem_image.mp hb'
    exact h g p hp (by simpa only [hpn] using hn)

def sourceOriginalPhysicalGhostUnseenPrimeRow434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ) : ℂ :=
  ∑ d : SourceOriginalPhysicalGhostPrimeBirthWitness434 SP sm BP bm M y,
    if ∀ g,∀ p ∈ (d g).2,bm g p ∉ seen then
      sourceOriginalPhysicalGhostPrimeBirthCoefficient434 SP sm BP bm M q rho N i V mu y d *
        F (sourceOriginalPhysicalGhostAtomOutput434 SP sm BP bm M y
          (sourceOriginalPhysicalGhostPrimeBirthLift434 SP sm BP bm M y d))
          (seen ∪ sourceOriginalPhysicalGhostPrimeBirthSet434 SP sm BP bm M y d)
    else 0

theorem source_original_PHYSICAL_G_unseen_prime_row434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ) :
    sourceOriginalPhysicalGhostAtomRow434 SP sm BP bm M q rho N i V mu y seen F =
    sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm M q rho N i V mu y seen F := by
  rw [source_original_PHYSICAL_G_atom_prime_birth_row434]
  unfold sourceOriginalPhysicalGhostPrimeBirthRow434 sourceOriginalPhysicalGhostUnseenPrimeRow434
  apply Finset.sum_congr rfl
  intro d hd
  dsimp only
  rw [propext (source_original_PHYSICAL_G_prime_birth_gate434 SP sm BP bm M hi y seen d),
    source_original_PHYSICAL_G_prime_birth_set434]
  by_cases h : ∀ g,∀ p ∈ (d g).2,bm g p ∉ seen
  · simp only [if_pos h]
  · simp only [if_neg h]

/-- Original symmetric G, with the exact global no-rebirth condition
written prime by prime. Its arbitrary joint continuation is unchanged. -/
theorem source_original_PHYSICAL_SYMMETRIC_G_unseen_prime_row434
    (cap : BG → ℕ) (J ell : ℕ)
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (q rho : ℝ) (N i : ℕ)
    (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen)
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    physicalMarkedSymmetricG SP sm BP bm J ell cap q rho N i Vs V mu y seen F =
    sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell)
      q rho N i V mu y seen F := by
  rw [source_original_PHYSICAL_SYMMETRIC_G_atom_row434
    SP sm BP bm cap J ell q rho N i Vs V mu hVs hmu y seen hy hcap F,
    source_original_PHYSICAL_G_unseen_prime_row434 SP sm BP bm (J+ell) hi]

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryPrimeBirthChain -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Exact G unseen-prime subset rows followed by literal source E rows on canonical
OLD representatives. Every global birth gate and common continuation
is preserved, with no internal orbit average or G OLD-position index. -/
def sourceOriginalPrimeBirthGEChain434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ) :
    (remaining start : ℕ) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
  | 0,start,F => fun y seen =>
      sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell) q rho N start V mu
        y seen F
  | n+1,start,F => fun y seen =>
      sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell) q rho N start V mu
        y seen
        (fun yg sg =>
          physicalOrientedBirthMarkedE SP sm BP bm J ell m cap patterns
            q rho Vs V mu
            (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
            zeta theta (physicalAlternatingSign start) k
            (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg
            (sourceOriginalPrimeBirthGEChain434 q rho Vs V mu K zeta theta k N n (start+1) F))

/-- Exact chain descent, uniform in all finite carriers, depths and joint
terminal tests. Only physical positivity and the original saturated caps
are needed in addition to the proved reachable source sector. -/
theorem source_original_MEMORY_prime_birth_chain_exact434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (n start : ℕ) (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen) :
    memorySourceGEChain SP sm BP bm J ell m patterns cap q rho Vs V mu K
      zeta theta k N n start F y seen =
    sourceOriginalPrimeBirthGEChain434 SP sm BP bm J ell m cap patterns q rho Vs V mu K
      zeta theta k N n start F y seen := by
  induction n generalizing start y seen with
  | zero =>
      exact source_original_PHYSICAL_SYMMETRIC_G_unseen_prime_row434 SP sm BP bm cap J ell hi
        q rho N start Vs V mu hVs hmu y seen hy hcap F
  | succ n ih =>
      simp only [memorySourceGEChain,sourceOriginalPrimeBirthGEChain434]
      symm
      rw [←source_original_PHYSICAL_SYMMETRIC_G_unseen_prime_row434 SP sm BP bm cap J ell hi
        q rho N start Vs V mu hVs hmu y seen hy hcap]
      apply source_original_SYMMETRIC_G_reachable_congr434 SP sm BP bm cap J ell
        q rho N start Vs V mu y seen hy
      intro yg sg hg
      rw [←source_original_SOURCE_SYMMETRIC_E_canonical434 SP sm BP bm cap J ell m patterns
        hcap yg sg hg q rho Vs V mu hVs hmu]
      apply source_original_SYMMETRIC_E_reachable_congr434 SP sm BP bm cap J ell m patterns
        q rho Vs V mu _ zeta theta _ k yg sg hg
      intro ye se he
      exact (ih (start+1) ye se he).symm

def sourceOriginalPrimeBirthMemoryRoot434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ) : ℂ :=
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  (physicalSourceBaselineProduct BP bm q N : ℂ) *
    ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y : ℂ) *
      star (physicalVacuum SP sm BP bm J ell y) *
      (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then
        sourceOriginalPrimeBirthGEChain434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta k N N 0
          (fun out _ => physicalVacuum SP sm BP bm J ell out)
          y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
      else 0)

/-- Full original root, with its outer physical Fock orbit mass, baseline
and both vacuum factors, equals the chain of actual marked rows. -/
theorem source_original_MEMORY_root_prime_birth_exact434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hVs : ∀ g,0 < Vs g)
    (hmu : ∀ g p,0 < physicalSourceMuTilde BP bm q (2*R) V g p) :
    memorySourceRoot SP sm BP bm J ell m patterns cap q rho Vs V K zeta theta k R =
    sourceOriginalPrimeBirthMemoryRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R := by
  unfold memorySourceRoot sourceOriginalPrimeBirthMemoryRoot434
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hv : physicalVacuum SP sm BP bm J ell y=0
  · simp only [hv,star_zero,mul_zero,zero_mul]
  · by_cases hn : (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
    · simp only [if_pos hn]
      rw [source_original_MEMORY_prime_birth_chain_exact434
        SP sm BP bm J ell m cap patterns hi hcap q rho Vs V _ hVs hmu K zeta theta k (2*R)
        _ (2*R) 0 y _ (source_original_MEMORY_initial_reachable434
          SP sm BP bm J ell y hv hn)]
    · simp only [if_neg hn]

/-- Applicable original finite root with actual unseen-prime G, original
source E, fixed phases and both vacuum/Fock endpoints. -/
theorem source_original_MEMORY_root_prime_birth_source_domain434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP sm BP bm cap q rho Vs V k R) :
    memorySourceRoot SP sm BP bm J ell m patterns cap q rho Vs V K zeta theta k R =
    sourceOriginalPrimeBirthMemoryRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R :=
  source_original_MEMORY_root_prime_birth_exact434 SP sm BP bm J ell m cap patterns
    hd.big_injective hd.cap_saturated q rho Vs V K zeta theta k R hd.Vsmall_pos
    (source_original_SOURCE_tilt_positive434 BP bm q hd.q_pos.le (2*R) V
      hd.Vbig_pos hd.big_above_visits)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryFrameChain -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Exact G unseen-prime subset rows followed by literal source E frame rows on canonical
OLD representatives. Every global birth gate and common continuation
is preserved, with no internal orbit average or summed G/E OLD-position indices. -/
def sourceOriginalFrameGEChain434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ) :
    (remaining start : ℕ) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
  | 0,start,F => fun y seen =>
      sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell) q rho N start V mu
        y seen F
  | n+1,start,F => fun y seen =>
      sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell) q rho N start V mu
        y seen
        (fun yg sg =>
          sourceOriginalSourceEFrameRow434 SP sm BP bm J ell m cap patterns
            q rho Vs V mu
            (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
            zeta theta (physicalAlternatingSign start) k
            (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg
            (sourceOriginalFrameGEChain434 q rho Vs V mu K zeta theta k N n (start+1) F))

/-- Exact chain descent, uniform in all finite carriers, depths and joint
terminal tests. Only physical positivity and the original saturated caps
are needed in addition to the proved reachable source sector. -/
theorem source_original_MEMORY_frame_chain_exact434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (n start : ℕ) (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen) :
    memorySourceGEChain SP sm BP bm J ell m patterns cap q rho Vs V mu K
      zeta theta k N n start F y seen =
    sourceOriginalFrameGEChain434 SP sm BP bm J ell m cap patterns q rho Vs V mu K
      zeta theta k N n start F y seen := by
  induction n generalizing start y seen with
  | zero =>
      exact source_original_PHYSICAL_SYMMETRIC_G_unseen_prime_row434 SP sm BP bm cap J ell hi
        q rho N start Vs V mu hVs hmu y seen hy hcap F
  | succ n ih =>
      simp only [memorySourceGEChain,sourceOriginalFrameGEChain434]
      symm
      rw [←source_original_PHYSICAL_SYMMETRIC_G_unseen_prime_row434 SP sm BP bm cap J ell hi
        q rho N start Vs V mu hVs hmu y seen hy hcap]
      apply source_original_SYMMETRIC_G_reachable_congr434 SP sm BP bm cap J ell
        q rho N start Vs V mu y seen hy
      intro yg sg hg
      have hproj := source_original_REACHABLE_canonical_projection434
        SP sm BP bm (J+ell) cap hcap yg sg hg
      have hcan : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
          (physicalFockProjection SP sm BP bm (J+ell) cap
            (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg)) sg := by
        rw [hproj]
        exact hg
      rw [←source_original_SOURCE_MARKED_E_frame_row434
        SP sm BP bm J ell m cap patterns q rho Vs V mu _ zeta theta _ k
        (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg hcan]
      rw [←source_original_SOURCE_SYMMETRIC_E_canonical434 SP sm BP bm cap J ell m patterns
        hcap yg sg hg q rho Vs V mu hVs hmu]
      apply source_original_SYMMETRIC_E_reachable_congr434 SP sm BP bm cap J ell m patterns
        q rho Vs V mu _ zeta theta _ k yg sg hg
      intro ye se he
      exact (ih (start+1) ye se he).symm

def sourceOriginalFrameMemoryRoot434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ) : ℂ :=
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  (physicalSourceBaselineProduct BP bm q N : ℂ) *
    ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y : ℂ) *
      star (physicalVacuum SP sm BP bm J ell y) *
      (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then
        sourceOriginalFrameGEChain434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta k N N 0
          (fun out _ => physicalVacuum SP sm BP bm J ell out)
          y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
      else 0)

/-- Full original root, with its outer physical Fock orbit mass, baseline
and both vacuum factors, equals the chain of actual marked rows. -/
theorem source_original_MEMORY_root_frame_exact434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hVs : ∀ g,0 < Vs g)
    (hmu : ∀ g p,0 < physicalSourceMuTilde BP bm q (2*R) V g p) :
    memorySourceRoot SP sm BP bm J ell m patterns cap q rho Vs V K zeta theta k R =
    sourceOriginalFrameMemoryRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R := by
  unfold memorySourceRoot sourceOriginalFrameMemoryRoot434
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hv : physicalVacuum SP sm BP bm J ell y=0
  · simp only [hv,star_zero,mul_zero,zero_mul]
  · by_cases hn : (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
    · simp only [if_pos hn]
      rw [source_original_MEMORY_frame_chain_exact434
        SP sm BP bm J ell m cap patterns hi hcap q rho Vs V _ hVs hmu K zeta theta k (2*R)
        _ (2*R) 0 y _ (source_original_MEMORY_initial_reachable434
          SP sm BP bm J ell y hv hn)]
    · simp only [if_neg hn]

/-- Applicable original finite root with actual unseen-prime G, original
source E, fixed phases and both vacuum/Fock endpoints. -/
theorem source_original_MEMORY_root_frame_source_domain434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP sm BP bm cap q rho Vs V k R) :
    memorySourceRoot SP sm BP bm J ell m patterns cap q rho Vs V K zeta theta k R =
    sourceOriginalFrameMemoryRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R :=
  source_original_MEMORY_root_frame_exact434 SP sm BP bm J ell m cap patterns
    hd.big_injective hd.cap_saturated q rho Vs V K zeta theta k R hd.Vsmall_pos
    (source_original_SOURCE_tilt_positive434 BP bm q hd.q_pos.le (2*R) V
      hd.Vbig_pos hd.big_above_visits)

/-- Applicable original root in the rho=1 frame representation.
The pre-existing exact full-root rho invariance is used algebraically;
no damping gain or source-domain assertion at rho=1 is assumed. -/
theorem source_original_MEMORY_root_frame_rho_one_source_domain434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP sm BP bm cap q rho Vs V k R) :
    memorySourceRoot SP sm BP bm J ell m patterns cap q rho Vs V K zeta theta k R =
    sourceOriginalFrameMemoryRoot434 SP sm BP bm J ell m cap patterns
      q 1 Vs V K zeta theta k R := by
  rw [source_original_memory_SOURCE_ROOT_rho_invariant434
    SP sm BP bm J ell m cap patterns q rho (ne_of_gt hd.rho_pos) Vs V K zeta theta k R]
  exact source_original_MEMORY_root_frame_exact434 SP sm BP bm J ell m cap patterns
    hd.big_injective hd.cap_saturated q 1 Vs V K zeta theta k R hd.Vsmall_pos
    (source_original_SOURCE_tilt_positive434 BP bm q hd.q_pos.le (2*R) V
      hd.Vbig_pos hd.big_above_visits)

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryFrameDomainWitness -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- A concrete nonempty instance of the exact algebraic source-domain
contract. This checks consistency of the row/root identity premises;
it does not assert any asymptotic positive-saving budget. -/
theorem source_original_MEMORY_frame_domain_witness434 :
    MemorySourceDomain
      (fun _ : Unit => Unit) (fun _ _ => 5)
      (fun _ : Unit => Unit) (fun _ _ => 7)
      (fun _ => 1)
      (1/4) (3/4) (fun _ => 1/5) (fun _ => 1/7) 1 1 := by
  refine {
    q_pos := by norm_num
    q_lt_one := by norm_num
    rho_pos := by norm_num
    rho_lt_one := by norm_num
    rho_sq := ?_
    R_pos := by norm_num
    k_ne := by norm_num
    small_prime := by intro g p; norm_num
    big_prime := by intro g p; norm_num
    small_injective := by
      intro x y h
      rcases x with ⟨⟨⟩,⟨⟩⟩
      rcases y with ⟨⟨⟩,⟨⟩⟩
      rfl
    big_injective := by
      intro x y h
      rcases x with ⟨⟨⟩,⟨⟩⟩
      rcases y with ⟨⟨⟩,⟨⟩⟩
      rfl
    disjoint := by intro gs ps gb pb; norm_num
    small_above_k := by intro g p; norm_num
    big_above_k := by intro g p; norm_num
    big_above_visits := by intro g p; norm_num
    Vsmall_eq := by intro g; simp
    Vbig_eq := by intro g; simp
    Vsmall_pos := by intro g; norm_num
    Vbig_pos := by intro g; norm_num
    cap_saturated := by intro g; norm_num }
  have he : (1/4 : ℝ)=(1/2:ℝ)^2 := by norm_num
  rw [he,Real.sqrt_sq_eq_abs]
  norm_num
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualOLDFirstCrossing -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 16000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

theorem source_original_OLD_G_sub434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (F A : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell)
      q rho N i V mu y seen (fun out st => F out st-A out st) =
    sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell)
      q rho N i V mu y seen F -
    sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell)
      q rho N i V mu y seen A := by
  unfold sourceOriginalPhysicalGhostUnseenPrimeRow434
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  split_ifs <;> ring

theorem source_original_OLD_E_sub434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (F A : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalSourceEFrameRow434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen (fun out st => F out st-A out st) =
    sourceOriginalSourceEFrameRow434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen F -
    sourceOriginalSourceEFrameRow434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen A := by
  unfold sourceOriginalSourceEFrameRow434
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  split_ifs <;> ring

/-- Exactly P E P at every E visit: source after G, target before next G.
All numerical seen gates, coefficients, orientation and joint tests remain. -/
def sourceOriginalOLDProjectedFrameGEChain434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N T : ℕ) :
    (remaining start : ℕ) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
  | 0,start,F => fun y seen =>
      sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell) q rho N start V mu y seen F
  | n+1,start,F => fun y seen =>
      sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell) q rho N start V mu
        y seen (fun yg sg =>
          if (∑ g : BG,(yg.2 g).2.card) ≤ T then
            sourceOriginalSourceEFrameRow434 SP sm BP bm J ell m cap patterns
              q rho Vs V mu
              (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
              zeta theta (physicalAlternatingSign start) k
              (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg
              (fun out st => if (∑ g : BG,(out.2 g).2.card) ≤ T then
                sourceOriginalOLDProjectedFrameGEChain434 q rho Vs V mu K zeta theta k N T
                  n (start+1) F out st else 0)
          else 0)

/-- Disjoint first-crossing recursion. Before the first failure both OLD
gates are imposed; afterwards the original full signed continuation is used.
A source failure and a target failure at the same visit are not double counted. -/
def sourceOriginalOLDFirstCrossingFrameGEChain434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N T : ℕ) :
    (remaining start : ℕ) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
  | 0,_,_ => fun _ _ => 0
  | n+1,start,F => fun y seen =>
      sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell) q rho N start V mu
        y seen (fun yg sg =>
          if (∑ g : BG,(yg.2 g).2.card) ≤ T then
            sourceOriginalSourceEFrameRow434 SP sm BP bm J ell m cap patterns
              q rho Vs V mu
              (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
              zeta theta (physicalAlternatingSign start) k
              (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg
              (fun out st => if (∑ g : BG,(out.2 g).2.card) ≤ T then
                sourceOriginalOLDFirstCrossingFrameGEChain434 q rho Vs V mu K zeta theta k N T
                  n (start+1) F out st
              else sourceOriginalFrameGEChain434 SP sm BP bm J ell m cap patterns
                q rho Vs V mu K zeta theta k N n (start+1) F out st)
          else
            sourceOriginalSourceEFrameRow434 SP sm BP bm J ell m cap patterns
              q rho Vs V mu
              (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
              zeta theta (physicalAlternatingSign start) k
              (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg
              (sourceOriginalFrameGEChain434 SP sm BP bm J ell m cap patterns
                q rho Vs V mu K zeta theta k N n (start+1) F))

/-- Exact signed discrepancy, with every first-crossing event retained.
This finite identity has no operator norm, tail or saving premise. -/
theorem source_original_MEMORY_OLD_first_crossing_partition434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N T : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (n start : ℕ) (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) :
    sourceOriginalFrameGEChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N n start F y seen -
    sourceOriginalOLDProjectedFrameGEChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T n start F y seen =
    sourceOriginalOLDFirstCrossingFrameGEChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T n start F y seen := by
  induction n generalizing start y seen with
  | zero => simp only [sourceOriginalFrameGEChain434,
      sourceOriginalOLDProjectedFrameGEChain434,sourceOriginalOLDFirstCrossingFrameGEChain434,sub_self]
  | succ n ih =>
      dsimp only [sourceOriginalFrameGEChain434,
        sourceOriginalOLDProjectedFrameGEChain434,sourceOriginalOLDFirstCrossingFrameGEChain434]
      rw [←source_original_OLD_G_sub434]
      congr 1
      funext yg sg
      by_cases hg : (∑ g : BG,(yg.2 g).2.card) ≤ T
      · simp only [if_pos hg]
        rw [←source_original_OLD_E_sub434]
        congr 1
        funext out st
        by_cases ht : (∑ g : BG,(out.2 g).2.card) ≤ T
        · simp only [if_pos ht]
          exact ih (start+1) out st
        · simp only [if_neg ht,sub_zero]
      · simp only [if_neg hg,sub_zero]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualOLDProjectorRoot -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Literal original marked symmetric G/E chain with P E P at every E.
The projectors inspect total pending OLD at the actual input and output. -/
def sourceOriginalOLDProjectedMemoryGEChain434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N T : ℕ) :
    (remaining start : ℕ) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
  | 0,start,F => fun y seen =>
      physicalMarkedSymmetricG SP sm BP bm J ell cap q rho N start Vs V mu y seen F
  | n+1,start,F => fun y seen =>
      physicalMarkedSymmetricG SP sm BP bm J ell cap q rho N start Vs V mu y seen
        (fun yg sg => if (∑ g : BG,(yg.2 g).2.card) ≤ T then
          physicalOrientedMarkedSymmetricE SP sm BP bm J ell m cap patterns
            q rho Vs V mu
            (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
            zeta theta (physicalAlternatingSign start) k yg sg
            (fun out st => if (∑ g : BG,(out.2 g).2.card) ≤ T then
              sourceOriginalOLDProjectedMemoryGEChain434 q rho Vs V mu K zeta theta k N T
                n (start+1) F out st else 0)
        else 0)

theorem source_original_MEMORY_OLD_projected_frame_exact434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N T : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (n start : ℕ) (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen) :
    sourceOriginalOLDProjectedMemoryGEChain434 SP sm BP bm J ell m cap patterns q rho Vs V mu K
      zeta theta k N T n start F y seen =
    sourceOriginalOLDProjectedFrameGEChain434 SP sm BP bm J ell m cap patterns q rho Vs V mu K
      zeta theta k N T n start F y seen := by
  induction n generalizing start y seen with
  | zero =>
      exact source_original_PHYSICAL_SYMMETRIC_G_unseen_prime_row434 SP sm BP bm cap J ell hi
        q rho N start Vs V mu hVs hmu y seen hy hcap F
  | succ n ih =>
      simp only [sourceOriginalOLDProjectedMemoryGEChain434,sourceOriginalOLDProjectedFrameGEChain434]
      symm
      rw [←source_original_PHYSICAL_SYMMETRIC_G_unseen_prime_row434 SP sm BP bm cap J ell hi
        q rho N start Vs V mu hVs hmu y seen hy hcap]
      apply source_original_SYMMETRIC_G_reachable_congr434 SP sm BP bm cap J ell
        q rho N start Vs V mu y seen hy
      intro yg sg hg
      by_cases hOld : (∑ g : BG,(yg.2 g).2.card) ≤ T
      · simp only [if_pos hOld]
        have hproj := source_original_REACHABLE_canonical_projection434
          SP sm BP bm (J+ell) cap hcap yg sg hg
        have hcan : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
            (physicalFockProjection SP sm BP bm (J+ell) cap
              (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg)) sg := by
          rw [hproj]
          exact hg
        rw [←source_original_SOURCE_MARKED_E_frame_row434
          SP sm BP bm J ell m cap patterns q rho Vs V mu _ zeta theta _ k
          (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg hcan]
        rw [←source_original_SOURCE_SYMMETRIC_E_canonical434 SP sm BP bm cap J ell m patterns
          hcap yg sg hg q rho Vs V mu hVs hmu]
        apply source_original_SYMMETRIC_E_reachable_congr434 SP sm BP bm cap J ell m patterns
          q rho Vs V mu _ zeta theta _ k yg sg hg
        intro ye se he
        by_cases ht : (∑ g : BG,(ye.2 g).2.card) ≤ T
        · simp only [if_pos ht]
          exact (ih (start+1) ye se he).symm
        · simp only [if_neg ht]
      · simp only [if_neg hOld]

def sourceOriginalOLDProjectedMemoryRoot434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T : ℕ) : ℂ :=
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  (physicalSourceBaselineProduct BP bm q N : ℂ) *
    ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y : ℂ) *
      star (physicalVacuum SP sm BP bm J ell y) *
      (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then
        sourceOriginalOLDProjectedMemoryGEChain434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta k N T N 0
          (fun out _ => physicalVacuum SP sm BP bm J ell out)
          y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
      else 0)

def sourceOriginalOLDFirstCrossingMemoryRoot434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T : ℕ) : ℂ :=
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  (physicalSourceBaselineProduct BP bm q N : ℂ) *
    ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y : ℂ) *
      star (physicalVacuum SP sm BP bm J ell y) *
      (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then
        sourceOriginalOLDFirstCrossingFrameGEChain434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta k N T N 0
          (fun out _ => physicalVacuum SP sm BP bm J ell out)
          y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
      else 0)

/-- Exact OLD-projector discrepancy for the ORIGINAL Memory source root.
The full physical baseline, Fock orbit masses, vacuum endpoints, initial
Nodup filter, all later seen gates and original orientation K are retained.
This identity does not yet assert that the discrepancy is small. -/
theorem source_original_MEMORY_OLD_root_first_crossing434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (hd : MemorySourceDomain SP sm BP bm cap q rho Vs V k R) :
    memorySourceRoot SP sm BP bm J ell m patterns cap q rho Vs V K zeta theta k R -
    sourceOriginalOLDProjectedMemoryRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T =
    sourceOriginalOLDFirstCrossingMemoryRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T := by
  unfold memorySourceRoot sourceOriginalOLDProjectedMemoryRoot434
    sourceOriginalOLDFirstCrossingMemoryRoot434
  dsimp only
  rw [←mul_sub,←Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hv : physicalVacuum SP sm BP bm J ell y=0
  · simp only [hv,star_zero,mul_zero,zero_mul,sub_zero]
  by_cases hn : (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
  · simp only [if_pos hn]
    have hy := source_original_MEMORY_initial_reachable434 SP sm BP bm J ell y hv hn
    have hmu := source_original_SOURCE_tilt_positive434 BP bm q hd.q_pos.le (2*R) V
      hd.Vbig_pos hd.big_above_visits
    rw [source_original_MEMORY_frame_chain_exact434 SP sm BP bm J ell m cap patterns
      hd.big_injective hd.cap_saturated q rho Vs V _ hd.Vsmall_pos hmu K
      zeta theta k (2*R) _ (2*R) 0 y _ hy]
    rw [source_original_MEMORY_OLD_projected_frame_exact434 SP sm BP bm J ell m cap patterns
      hd.big_injective hd.cap_saturated q rho Vs V _ hd.Vsmall_pos hmu K
      zeta theta k (2*R) T _ (2*R) 0 y _ hy]
    rw [←mul_sub,source_original_MEMORY_OLD_first_crossing_partition434]
  · simp only [if_neg hn,mul_zero,sub_zero]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualOLDProjectorRho -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Both literal OLD projectors commute with the exact endpoint density
gauge. All physical seen/parity tests remain arbitrary. -/
theorem source_original_MEMORY_OLD_projected_chain_rho_cancellation434
    (q rho : ℝ) (hrho : rho ≠ 0)
    (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N T : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (n start : ℕ) (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) :
    sourceOriginalMemoryOldOutput434 SP sm BP bm J ell rho y *
      sourceOriginalOLDProjectedMemoryGEChain434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta k N T n start
        (fun out st => sourceOriginalMemoryOldOutput434 SP sm BP bm J ell rho out * F out st)
        y seen =
    sourceOriginalOLDProjectedMemoryGEChain434 SP sm BP bm J ell m cap patterns
      q 1 Vs V mu K zeta theta k N T n start F y seen := by
  induction n generalizing start y seen with
  | zero =>
      exact source_original_memory_SYMMETRIC_G_rho_cancellation434
        SP sm BP bm J ell cap q rho hrho N start Vs V mu y seen F
  | succ n ih =>
      dsimp only [sourceOriginalOLDProjectedMemoryGEChain434]
      simp_rw [source_original_memory_SYMMETRIC_E_OLD_sandwich434
        SP sm BP bm J ell m cap patterns q rho Vs V mu]
      have hInside (out : FullPhysicalOutput SP sm BP bm (J+ell)) (st : Finset ℕ) :
          sourceOriginalMemoryOldOutput434 SP sm BP bm J ell rho out *
            (if (∑ g : BG,(out.2 g).2.card) ≤ T then
              sourceOriginalOLDProjectedMemoryGEChain434 SP sm BP bm J ell m cap patterns
                q rho Vs V mu K zeta theta k N T n (start+1)
                (fun z s => sourceOriginalMemoryOldOutput434 SP sm BP bm J ell rho z * F z s)
                out st else 0) =
            (if (∑ g : BG,(out.2 g).2.card) ≤ T then
              sourceOriginalOLDProjectedMemoryGEChain434 SP sm BP bm J ell m cap patterns
                q 1 Vs V mu K zeta theta k N T n (start+1) F out st else 0) := by
        by_cases ht : (∑ g : BG,(out.2 g).2.card) ≤ T
        · simp only [if_pos ht]
          exact ih (start+1) out st
        · simp only [if_neg ht,mul_zero]
      simp_rw [hInside]
      simpa only [mul_ite,mul_zero] using
        source_original_memory_SYMMETRIC_G_rho_cancellation434
          SP sm BP bm J ell cap q rho hrho N start Vs V mu y seen
          (fun yg sg => if (∑ g : BG,(yg.2 g).2.card) ≤ T then
            physicalOrientedMarkedSymmetricE SP sm BP bm J ell m cap patterns
              q 1 Vs V mu
              (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
              zeta theta (physicalAlternatingSign start) k yg sg
              (fun out st => if (∑ g : BG,(out.2 g).2.card) ≤ T then
                sourceOriginalOLDProjectedMemoryGEChain434 SP sm BP bm J ell m cap patterns
                  q 1 Vs V mu K zeta theta k N T n (start+1) F out st else 0)
            else 0)

/-- Genuine original projected root is rho invariant, including the
baseline, all Fock masses and both vacuum boundaries. -/
theorem source_original_MEMORY_OLD_projected_root_rho_invariant434
    (q rho : ℝ) (hrho : rho ≠ 0) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T : ℕ) :
    sourceOriginalOLDProjectedMemoryRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T =
    sourceOriginalOLDProjectedMemoryRoot434 SP sm BP bm J ell m cap patterns
      q 1 Vs V K zeta theta k R T := by
  have hVac (y : FullPhysicalOutput SP sm BP bm (J+ell)) :
      sourceOriginalMemoryOldOutput434 SP sm BP bm J ell rho y *
        physicalVacuum SP sm BP bm J ell y = physicalVacuum SP sm BP bm J ell y := by
    by_cases hv : ∀ g : BG,(y.2 g).2=0
    · simp [physicalVacuum,hv,sourceOriginalMemoryOldOutput434]
    · simp [physicalVacuum,hv]
  unfold sourceOriginalOLDProjectedMemoryRoot434
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hv : ∀ g : BG,(y.2 g).2=0
  · have hOld : sourceOriginalMemoryOldOutput434 SP sm BP bm J ell rho y=1 := by
      simp [sourceOriginalMemoryOldOutput434,hv]
    have hh := source_original_MEMORY_OLD_projected_chain_rho_cancellation434
      SP sm BP bm J ell m cap patterns q rho hrho Vs V
      (physicalSourceMuTilde BP bm q (2*R) V) K zeta theta k (2*R) T
      (fun out _ => physicalVacuum SP sm BP bm J ell out) (2*R) 0 y
      (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
    simp_rw [hVac] at hh
    rw [hOld,one_mul] at hh
    rw [hh]
  · simp [physicalVacuum,hv]

/-- Consequently the FULL signed projector discrepancy is also invariant.
rho cannot supply any uncharged decay in a claimed OLD-removal bound. -/
theorem source_original_MEMORY_OLD_discrepancy_rho_invariant434
    (q rho : ℝ) (hrho : rho ≠ 0) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T : ℕ) :
    memorySourceRoot SP sm BP bm J ell m patterns cap q rho Vs V K zeta theta k R -
      sourceOriginalOLDProjectedMemoryRoot434 SP sm BP bm J ell m cap patterns
        q rho Vs V K zeta theta k R T =
    memorySourceRoot SP sm BP bm J ell m patterns cap q 1 Vs V K zeta theta k R -
      sourceOriginalOLDProjectedMemoryRoot434 SP sm BP bm J ell m cap patterns
        q 1 Vs V K zeta theta k R T := by
  rw [source_original_memory_SOURCE_ROOT_rho_invariant434 SP sm BP bm J ell m cap patterns
    q rho hrho Vs V K zeta theta k R,
    source_original_MEMORY_OLD_projected_root_rho_invariant434 SP sm BP bm J ell m cap patterns
      q rho hrho Vs V K zeta theta k R T]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalGhostSubsetPartition -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

def sourceOriginalSubsetPartitionEquiv434
    {U : Type} [Fintype U] [DecidableEq U] (S : Finset U)
    (p : U → Prop) [DecidablePred p] :
    {A : Finset U // A ∈ S.powerset} ≃
      {A : Finset U // A ∈ (S.filter p).powerset} ×
      {B : Finset U // B ∈ (S.filter (fun u => ¬p u)).powerset} where
  toFun A :=
    (⟨A.1.filter p,Finset.mem_powerset.mpr (by
      intro a ha
      obtain ⟨ha,hp⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨(Finset.mem_powerset.mp A.2) ha,hp⟩)⟩,
     ⟨A.1.filter (fun u => ¬p u),Finset.mem_powerset.mpr (by
      intro a ha
      obtain ⟨ha,hp⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨(Finset.mem_powerset.mp A.2) ha,hp⟩)⟩)
  invFun d := ⟨d.1.1 ∪ d.2.1,Finset.mem_powerset.mpr (by
    intro a ha
    rcases Finset.mem_union.mp ha with h|h
    · exact (Finset.mem_filter.mp ((Finset.mem_powerset.mp d.1.2) h)).1
    · exact (Finset.mem_filter.mp ((Finset.mem_powerset.mp d.2.2) h)).1)⟩
  left_inv A := by
    apply Subtype.ext
    ext a
    simp only [Finset.mem_union,Finset.mem_filter]
    tauto
  right_inv d := by
    apply Prod.ext
    · apply Subtype.ext
      ext a
      have ha : a ∈ d.1.1 → p a :=
        fun h => (Finset.mem_filter.mp ((Finset.mem_powerset.mp d.1.2) h)).2
      have hb : a ∈ d.2.1 → ¬p a :=
        fun h => (Finset.mem_filter.mp ((Finset.mem_powerset.mp d.2.2) h)).2
      simp only [Finset.mem_filter,Finset.mem_union]
      tauto
    · apply Subtype.ext
      ext a
      have ha : a ∈ d.1.1 → p a :=
        fun h => (Finset.mem_filter.mp ((Finset.mem_powerset.mp d.1.2) h)).2
      have hb : a ∈ d.2.1 → ¬p a :=
        fun h => (Finset.mem_filter.mp ((Finset.mem_powerset.mp d.2.2) h)).2
      simp only [Finset.mem_filter,Finset.mem_union]
      tauto

def sourceOriginalUnivSubsetEquiv434
    {U : Type} [Fintype U] [DecidableEq U] :
    Finset U ≃ {B : Finset U // B ∈ (Finset.univ : Finset U).powerset} where
  toFun B := ⟨B,Finset.mem_powerset.mpr (Finset.subset_univ _)⟩
  invFun B := B.1
  left_inv _ := rfl
  right_inv _ := rfl

def sourceOriginalPairRegroupEquiv434 {A B C D : Type} :
    (A × B) × (C × D) ≃ (A × C) × (B × D) where
  toFun x := ((x.1.1,x.2.1),(x.1.2,x.2.2))
  invFun x := ((x.1.1,x.2.1),(x.1.2,x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]
variable (S : Finset (Atom P modulus)) (background : Finset P)

abbrev SourceOriginalRestrictedPrimeBirthChoice434
    (pool : Finset P) :=
  {A : Finset (Atom P modulus) // A ∈ S.powerset} ×
    {B : Finset P // B ∈ pool.powerset}

def sourceOriginalRestrictedPrimeBirthLift434 (pool : Finset P)
    (d : SourceOriginalRestrictedPrimeBirthChoice434 modulus S pool) :
    SourceOriginalGroupPrimeBirthChoice434 modulus S := (d.1,d.2.1)

def sourceOriginalGroupGhostPartitionEquiv434 :
    SourceOriginalGroupPrimeBirthChoice434 modulus S ≃
    SourceOriginalRestrictedPrimeBirthChoice434 modulus
      (S.filter (fun a => a.1 ∈ background))
      (Finset.univ.filter (fun p => p ∈ background)) ×
    SourceOriginalRestrictedPrimeBirthChoice434 modulus
      (S.filter (fun a => a.1 ∉ background))
      (Finset.univ.filter (fun p => p ∉ background)) :=
  (Equiv.prodCongr
    (sourceOriginalSubsetPartitionEquiv434 S (fun a => a.1 ∈ background))
    (sourceOriginalUnivSubsetEquiv434.trans
      (sourceOriginalSubsetPartitionEquiv434 Finset.univ (fun p => p ∈ background)))).trans
    sourceOriginalPairRegroupEquiv434

theorem source_original_GROUP_G_background_weight434
    (alpha chi gamma : ℂ) (mu : P → ℂ)
    (a : SourceOriginalRestrictedPrimeBirthChoice434 modulus
      (S.filter (fun a => a.1 ∈ background))
      (Finset.univ.filter (fun p => p ∈ background)))
    (b : SourceOriginalRestrictedPrimeBirthChoice434 modulus
      (S.filter (fun a => a.1 ∉ background))
      (Finset.univ.filter (fun p => p ∉ background))) :
    sourceOriginalGroupPrimeBirthWeight434 modulus S alpha chi gamma mu
      ((sourceOriginalGroupGhostPartitionEquiv434 modulus S background).symm (a,b)) =
    sourceOriginalGroupPrimeBirthWeight434 modulus
      (S.filter (fun a => a.1 ∈ background)) alpha chi gamma mu
      (sourceOriginalRestrictedPrimeBirthLift434 modulus _ _ a) *
    sourceOriginalGroupPrimeBirthWeight434 modulus
      (S.filter (fun a => a.1 ∉ background)) alpha chi gamma mu
      (sourceOriginalRestrictedPrimeBirthLift434 modulus _ _ b) := by
  have hdis : Disjoint (S.filter (fun a => a.1 ∈ background))
      (S.filter (fun a => a.1 ∉ background)) := by
    apply Finset.disjoint_left.mpr
    intro z hz hw
    exact (Finset.mem_filter.mp hw).2 (Finset.mem_filter.mp hz).2
  have hpart : (S.filter (fun a => a.1 ∈ background)) ∪
      (S.filter (fun a => a.1 ∉ background))=S := by
    ext z
    simp only [Finset.mem_union,Finset.mem_filter]
    tauto
  have hS := Finset.card_union_of_disjoint hdis
  rw [hpart] at hS
  have ha := Finset.mem_powerset.mp a.1.2
  have hb := Finset.mem_powerset.mp b.1.2
  have hdA : Disjoint a.1.1 b.1.1 := hdis.mono ha hb
  have hdB : Disjoint a.2.1 b.2.1 := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (Finset.mem_filter.mp ((Finset.mem_powerset.mp b.2.2) hq)).2
      (Finset.mem_filter.mp ((Finset.mem_powerset.mp a.2.2) hp)).2
  have hac := Finset.card_le_card ha
  have hbc := Finset.card_le_card hb
  have hc : S.card-(a.1.1.card+b.1.1.card) =
      ((S.filter (fun a => a.1 ∈ background)).card-a.1.1.card) +
      ((S.filter (fun a => a.1 ∉ background)).card-b.1.1.card) := by omega
  change alpha^(a.1.1 ∪ b.1.1).card *
      chi^(S.card-(a.1.1 ∪ b.1.1).card) *
      gamma^(a.2.1 ∪ b.2.1).card * (∏ p ∈ a.2.1 ∪ b.2.1,mu p) =
    (alpha^a.1.1.card * chi^((S.filter (fun a => a.1 ∈ background)).card-a.1.1.card) *
      gamma^a.2.1.card * (∏ p ∈ a.2.1,mu p)) *
    (alpha^b.1.1.card * chi^((S.filter (fun a => a.1 ∉ background)).card-b.1.1.card) *
      gamma^b.2.1.card * (∏ p ∈ b.2.1,mu p))
  rw [Finset.card_union_of_disjoint hdA,Finset.card_union_of_disjoint hdB,
    hc,Finset.prod_union hdB,pow_add,pow_add,pow_add]
  ring

/-- Exact background/active G decomposition with the entire joint test
inside the double sum. The cardinalities and all signed weights split
by actual disjoint subsets, without a count or independence assumption. -/
theorem source_original_GROUP_G_background_split434
    (alpha chi gamma : ℂ) (mu : P → ℂ)
    (H : SourceOriginalGroupPrimeBirthChoice434 modulus S → ℂ) :
    (∑ d : SourceOriginalGroupPrimeBirthChoice434 modulus S,
      sourceOriginalGroupPrimeBirthWeight434 modulus S alpha chi gamma mu d * H d) =
    ∑ a : SourceOriginalRestrictedPrimeBirthChoice434 modulus
      (S.filter (fun a => a.1 ∈ background))
      (Finset.univ.filter (fun p => p ∈ background)),
    ∑ b : SourceOriginalRestrictedPrimeBirthChoice434 modulus
      (S.filter (fun a => a.1 ∉ background))
      (Finset.univ.filter (fun p => p ∉ background)),
      (sourceOriginalGroupPrimeBirthWeight434 modulus
        (S.filter (fun a => a.1 ∈ background)) alpha chi gamma mu
        (sourceOriginalRestrictedPrimeBirthLift434 modulus _ _ a) *
       sourceOriginalGroupPrimeBirthWeight434 modulus
        (S.filter (fun a => a.1 ∉ background)) alpha chi gamma mu
        (sourceOriginalRestrictedPrimeBirthLift434 modulus _ _ b)) *
      H ((sourceOriginalGroupGhostPartitionEquiv434 modulus S background).symm (a,b)) := by
  have he :
      (∑ d : SourceOriginalGroupPrimeBirthChoice434 modulus S,
        sourceOriginalGroupPrimeBirthWeight434 modulus S alpha chi gamma mu d * H d) =
      ∑ d : SourceOriginalRestrictedPrimeBirthChoice434 modulus
          (S.filter (fun a => a.1 ∈ background))
          (Finset.univ.filter (fun p => p ∈ background)) ×
        SourceOriginalRestrictedPrimeBirthChoice434 modulus
          (S.filter (fun a => a.1 ∉ background))
          (Finset.univ.filter (fun p => p ∉ background)),
        sourceOriginalGroupPrimeBirthWeight434 modulus S alpha chi gamma mu
          ((sourceOriginalGroupGhostPartitionEquiv434 modulus S background).symm d) *
        H ((sourceOriginalGroupGhostPartitionEquiv434 modulus S background).symm d) := by
    symm
    apply Fintype.sum_equiv (sourceOriginalGroupGhostPartitionEquiv434 modulus S background).symm
    intro d
    rfl
  rw [he,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [source_original_GROUP_G_background_weight434]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPhysicalGhostPartition -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

def sourceOriginalPiPairEquiv434 {I : Type} (A B : I → Type) :
    ((i : I) → A i × B i) ≃ ((i : I) → A i) × ((i : I) → B i) where
  toFun x := (fun i => (x i).1,fun i => (x i).2)
  invFun x := fun i => (x.1 i,x.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ)
variable (background : (g : BG) → Finset (BP g))
variable (y : FullPhysicalOutput SP sm BP bm M)

abbrev SourceOriginalGhostBackgroundChoice434 :=
  (g : BG) → SourceOriginalRestrictedPrimeBirthChoice434 (bm g)
    (((y.2 g).2.toFinset.filter (fun z => z.2=0)).filter (fun z => z.1 ∈ background g))
    (Finset.univ.filter (fun p => p ∈ background g))

abbrev SourceOriginalGhostActiveChoice434 :=
  (g : BG) → SourceOriginalRestrictedPrimeBirthChoice434 (bm g)
    (((y.2 g).2.toFinset.filter (fun z => z.2=0)).filter (fun z => z.1 ∉ background g))
    (Finset.univ.filter (fun p => p ∉ background g))

def sourceOriginalPhysicalGhostPartitionEquiv434 :
    SourceOriginalPhysicalGhostPrimeBirthWitness434 SP sm BP bm M y ≃
    SourceOriginalGhostBackgroundChoice434 SP sm BP bm M background y ×
      SourceOriginalGhostActiveChoice434 SP sm BP bm M background y :=
  (Equiv.piCongrRight (fun g => sourceOriginalGroupGhostPartitionEquiv434 (bm g)
    ((y.2 g).2.toFinset.filter (fun z => z.2=0)) (background g))).trans
    (sourceOriginalPiPairEquiv434 _ _)

def sourceOriginalPhysicalGhostRecombine434
    (a : SourceOriginalGhostBackgroundChoice434 SP sm BP bm M background y)
    (b : SourceOriginalGhostActiveChoice434 SP sm BP bm M background y) :
    SourceOriginalPhysicalGhostPrimeBirthWitness434 SP sm BP bm M y :=
  (sourceOriginalPhysicalGhostPartitionEquiv434 SP sm BP bm M background y).symm (a,b)

def sourceOriginalGhostBackgroundCoefficient434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (a : SourceOriginalGhostBackgroundChoice434 SP sm BP bm M background y) : ℂ :=
  ∏ g,sourceOriginalGroupPrimeBirthWeight434 (bm g)
    (((y.2 g).2.toFinset.filter (fun z => z.2=0)).filter (fun z => z.1 ∈ background g))
    (-((sourceVisitEta q N i:ℝ):ℂ)/(rho:ℂ))
    (((sourceVisitQ q N i:ℝ):ℂ)/(rho:ℂ)^2)
    (-((sourceVisitEta q N i:ℝ):ℂ)*(V g:ℂ)/(rho:ℂ))
    (fun p => (mu g p:ℂ)) (sourceOriginalRestrictedPrimeBirthLift434 (bm g) _ _ (a g))

def sourceOriginalGhostActiveCoefficient434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (b : SourceOriginalGhostActiveChoice434 SP sm BP bm M background y) : ℂ :=
  ∏ g,sourceOriginalGroupPrimeBirthWeight434 (bm g)
    (((y.2 g).2.toFinset.filter (fun z => z.2=0)).filter (fun z => z.1 ∉ background g))
    (-((sourceVisitEta q N i:ℝ):ℂ)/(rho:ℂ))
    (((sourceVisitQ q N i:ℝ):ℂ)/(rho:ℂ)^2)
    (-((sourceVisitEta q N i:ℝ):ℂ)*(V g:ℂ)/(rho:ℂ))
    (fun p => (mu g p:ℂ)) (sourceOriginalRestrictedPrimeBirthLift434 (bm g) _ _ (b g))

theorem source_original_PHYSICAL_G_partition_coefficient434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (a : SourceOriginalGhostBackgroundChoice434 SP sm BP bm M background y)
    (b : SourceOriginalGhostActiveChoice434 SP sm BP bm M background y) :
    sourceOriginalPhysicalGhostPrimeBirthCoefficient434 SP sm BP bm M q rho N i V mu y
      (sourceOriginalPhysicalGhostRecombine434 SP sm BP bm M background y a b) =
    sourceOriginalGhostBackgroundCoefficient434 SP sm BP bm M background y q rho N i V mu a *
    sourceOriginalGhostActiveCoefficient434 SP sm BP bm M background y q rho N i V mu b := by
  unfold sourceOriginalPhysicalGhostPrimeBirthCoefficient434
    sourceOriginalGhostBackgroundCoefficient434 sourceOriginalGhostActiveCoefficient434
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g hg
  exact source_original_GROUP_G_background_weight434 (bm g)
    ((y.2 g).2.toFinset.filter (fun z => z.2=0)) (background g)
    _ _ _ _ (a g) (b g)

theorem source_original_PHYSICAL_G_partition_gate434
    (seen : Finset ℕ)
    (a : SourceOriginalGhostBackgroundChoice434 SP sm BP bm M background y)
    (b : SourceOriginalGhostActiveChoice434 SP sm BP bm M background y) :
    (∀ g,∀ p ∈ (sourceOriginalPhysicalGhostRecombine434 SP sm BP bm M background y a b g).2,
      bm g p ∉ seen) ↔
    ((∀ g,∀ p ∈ (a g).2.1,bm g p ∉ seen) ∧
      (∀ g,∀ p ∈ (b g).2.1,bm g p ∉ seen)) := by
  change (∀ g,∀ p ∈ (a g).2.1 ∪ (b g).2.1,bm g p ∉ seen) ↔ _
  constructor
  · intro h
    exact ⟨fun g p hp => h g p (Finset.mem_union_left _ hp),
      fun g p hp => h g p (Finset.mem_union_right _ hp)⟩
  · rintro ⟨ha,hb⟩ g p hp
    rcases Finset.mem_union.mp hp with hp|hp
    · exact ha g p hp
    · exact hb g p hp

theorem source_original_PHYSICAL_G_partition_births434
    (a : SourceOriginalGhostBackgroundChoice434 SP sm BP bm M background y)
    (b : SourceOriginalGhostActiveChoice434 SP sm BP bm M background y) :
    sourceOriginalPhysicalGhostPrimeBirthSet434 SP sm BP bm M y
      (sourceOriginalPhysicalGhostRecombine434 SP sm BP bm M background y a b) =
    (Finset.univ.biUnion (fun g => (a g).2.1.image (bm g))) ∪
      (Finset.univ.biUnion (fun g => (b g).2.1.image (bm g))) := by
  change (Finset.univ.biUnion (fun g => ((a g).2.1 ∪ (b g).2.1).image (bm g))) = _
  ext n
  simp only [Finset.mem_biUnion,Finset.mem_image,Finset.mem_union,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨g,p,hp,hpn⟩
    rcases hp with hp|hp
    · exact Or.inl ⟨g,p,hp,hpn⟩
    · exact Or.inr ⟨g,p,hp,hpn⟩
  · rintro (⟨g,p,hp,hpn⟩|⟨g,p,hp,hpn⟩)
    · exact ⟨g,p,Or.inl hp,hpn⟩
    · exact ⟨g,p,Or.inr hp,hpn⟩

/-- Exact weighted reindexing for all groups simultaneously. No
factorization of the joint observation H is used or needed. -/
theorem source_original_PHYSICAL_G_partition_joint_sum434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (H : SourceOriginalPhysicalGhostPrimeBirthWitness434 SP sm BP bm M y → ℂ) :
    (∑ d : SourceOriginalPhysicalGhostPrimeBirthWitness434 SP sm BP bm M y,
      sourceOriginalPhysicalGhostPrimeBirthCoefficient434 SP sm BP bm M q rho N i V mu y d * H d) =
    ∑ ab : SourceOriginalGhostBackgroundChoice434 SP sm BP bm M background y ×
        SourceOriginalGhostActiveChoice434 SP sm BP bm M background y,
      (sourceOriginalGhostBackgroundCoefficient434 SP sm BP bm M background y q rho N i V mu ab.1 *
        sourceOriginalGhostActiveCoefficient434 SP sm BP bm M background y q rho N i V mu ab.2) *
      H (sourceOriginalPhysicalGhostRecombine434 SP sm BP bm M background y ab.1 ab.2) := by
  symm
  apply Fintype.sum_equiv (sourceOriginalPhysicalGhostPartitionEquiv434 SP sm BP bm M background y).symm
  intro d
  rw [←source_original_PHYSICAL_G_partition_coefficient434]
  rfl
end Green64Analytic.CorrelationSquare

end

end

