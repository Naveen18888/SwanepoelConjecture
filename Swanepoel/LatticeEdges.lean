module
public import Swanepoel.LatticeShape
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def latticeConfigurationIso (S : Finset LatticeSite) {n : ℕ} (hn : S.card = n) :
    (latticeConfiguration S hn).graph ≃g latticeGraph S where
  toEquiv := (S.equivFinOfCardEq hn).symm
  map_rel_iff' := by
    intro i j
    change LatticeAdj _ _ ↔ (i ≠ j ∧ dist (latticePoint _) (latticePoint _) = 1)
    rw [lattice_contact]
    constructor
    · intro h
      refine ⟨?_, h⟩
      intro he
      subst j
      have hd := (lattice_contact _ _).mpr h
      simp at hd
    · exact And.right

def latticeVal (S : Finset LatticeSite) : S ↪ LatticeSite :=
  ⟨Subtype.val, Subtype.val_injective⟩

theorem lattice_edges (S : Finset LatticeSite) :
    (latticeGraph S).edgeFinset.map (latticeVal S).sym2Map =
      ((S.filter (fun p => east p ∈ S)).image (fun p => s(p, east p))) ∪
      ((S.filter (fun p => north p ∈ S)).image (fun p => s(p, north p))) := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp he
    revert hf
    refine Sym2.inductionOn f ?_
    intro p q hpq
    have ha : LatticeAdj p.val q.val :=
      SimpleGraph.mem_edgeFinset.mp hpq
    change s(p.val, q.val) ∈ _
    rcases ha with h | h | h | h
    · have hq : east p.val = q.val := Prod.ext h.1 h.2
      exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨p.val, Finset.mem_filter.mpr ⟨p.property, hq ▸ q.property⟩,
          Sym2.eq_iff.mpr (Or.inl ⟨rfl, hq⟩)⟩)
    · have hp : east q.val = p.val := Prod.ext h.1 h.2
      exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨q.val, Finset.mem_filter.mpr ⟨q.property, hp ▸ p.property⟩,
          Sym2.eq_iff.mpr (Or.inr ⟨rfl, hp⟩)⟩)
    · have hq : north p.val = q.val := Prod.ext h.1 h.2
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨p.val, Finset.mem_filter.mpr ⟨p.property, hq ▸ q.property⟩,
          Sym2.eq_iff.mpr (Or.inl ⟨rfl, hq⟩)⟩)
    · have hp : north q.val = p.val := Prod.ext h.1 h.2
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨q.val, Finset.mem_filter.mpr ⟨q.property, hp ▸ p.property⟩,
          Sym2.eq_iff.mpr (Or.inr ⟨rfl, hp⟩)⟩)
  · intro he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hp, hq⟩ := Finset.mem_filter.mp hp
      refine Finset.mem_map.mpr ⟨s((⟨p,hp⟩ : S), (⟨east p,hq⟩ : S)), ?_, rfl⟩
      apply SimpleGraph.mem_edgeFinset.mpr
      change LatticeAdj p (east p)
      simp [LatticeAdj, east]
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hp, hq⟩ := Finset.mem_filter.mp hp
      refine Finset.mem_map.mpr ⟨s((⟨p,hp⟩ : S), (⟨north p,hq⟩ : S)), ?_, rfl⟩
      apply SimpleGraph.mem_edgeFinset.mpr
      change LatticeAdj p (north p)
      simp [LatticeAdj, north]

theorem lattice_edge_count (S : Finset LatticeSite) :
    (latticeGraph S).edgeFinset.card =
      (S.filter (fun p => east p ∈ S)).card + (S.filter (fun p => north p ∈ S)).card := by
  classical
  have hx : Function.Injective (fun p : LatticeSite => s(p, east p)) := by
    intro p q h
    rcases Sym2.eq_iff.mp h with h | h
    · exact h.1
    · have h1 := congrArg Prod.fst h.1
      have h2 := congrArg Prod.fst h.2
      simp only [east] at h1 h2
      omega
  have hy : Function.Injective (fun p : LatticeSite => s(p, north p)) := by
    intro p q h
    rcases Sym2.eq_iff.mp h with h | h
    · exact h.1
    · have h1 := congrArg Prod.snd h.1
      have h2 := congrArg Prod.snd h.2
      simp only [north] at h1 h2
      omega
  have hd : Disjoint ((S.filter (fun p => east p ∈ S)).image (fun p => s(p,east p)))
      ((S.filter (fun p => north p ∈ S)).image (fun p => s(p,north p))) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp he
    obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hf
    rcases Sym2.eq_iff.mp (hp.trans hq.symm) with h | h
    all_goals
      have h1 := congrArg Prod.fst h.1
      have h2 := congrArg Prod.fst h.2
      simp only [east, north] at h1 h2
      omega
  have hc := congrArg Finset.card (lattice_edges S)
  simpa only [Finset.card_map, Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ hx, Finset.card_image_of_injective _ hy] using hc

theorem latticeConfiguration_edgeCount (S : Finset LatticeSite) {n : ℕ} (hn : S.card = n) :
    (latticeConfiguration S hn).edgeCount =
      (S.filter (fun p => east p ∈ S)).card + (S.filter (fun p => north p ∈ S)).card := by
  have he := (latticeConfigurationIso S hn).card_edgeFinset_eq
  rw [lattice_edge_count] at he
  simpa only [PennyGraph.edgeCount, SimpleGraph.edgeFinset_card,
    ← Nat.card_eq_fintype_card] using he

theorem gridShape_edgeCount (w h r : ℕ) (hh : 1 ≤ h) (hr : r ≤ w)
    {n : ℕ} (hn : (gridShape w h r).card = n) :
    (latticeConfiguration (gridShape w h r) hn).edgeCount =
      (w-1)*h+(r-1) + (w*(h-1)+r) := by
  rw [latticeConfiguration_edgeCount, gridShape_east _ _ _ hr,
    gridShape_north _ _ _ hh hr, gridShape_card, gridShape_card]

end Swanepoel
