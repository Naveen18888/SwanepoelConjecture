module
public import Swanepoel.TrackCardinality
public import Swanepoel.EdgeNeighbourhood
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def sourceNormal {n : ℕ} {G : PennyGraph n} (e : OrientedEdge G) : Plane :=
  -quarterTurn (carriedVector e)

theorem quarterTurn_neg (u : Plane) : quarterTurn (-u) = -quarterTurn u := by
  ext i
  fin_cases i <;> simp [quarterTurn]

theorem sourceNormal_norm {n : ℕ} {G : PennyGraph n} (e : OrientedEdge G) :
    ‖sourceNormal e‖ = 1 := by
  rw [sourceNormal, norm_neg, quarterTurn_norm, carriedVector_norm]

theorem source_same_component_eq_or_opposite {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {e f : OrientedEdge G}
    (he : SpineSource e) (hf : SpineSource f)
    (hc : edgeComponent f = edgeComponent e) :
    f = e ∨ carriedVector f = -carriedVector e := by
  obtain ⟨s, t, _, _, hp, hall⟩ := component_spine_iff ht e
  have hse : s = e := source_path_eq he hp.1
  rcases (hall f).mp hc with h | h
  · exact Or.inl ((source_path_eq hf h.1).symm.trans hse)
  · right
    have htf : reverseEdge t = f := source_path_eq hf h.1
    rw [← htf, reverseEdge_vector]
    have hv : carriedVector s = carriedVector t := positive_path_vector_eq (hp.1.trans hp.2)
    rw [hse] at hv
    exact congrArg Neg.neg hv.symm

theorem source_normals_opposite {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {e f : OrientedEdge G}
    (he : SpineSource e) (hf : SpineSource f)
    (hc : edgeComponent f = edgeComponent e) (hne : f ≠ e) :
    sourceNormal f = -sourceNormal e := by
  have hv := (source_same_component_eq_or_opposite ht he hf hc).resolve_left hne
  simp only [sourceNormal, hv, quarterTurn_neg, neg_neg]

theorem source_component_injective_in_open_semicircle {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) (v : Plane) {e f : OrientedEdge G}
    (he : SpineSource e) (hf : SpineSource f)
    (hev : 0 < inner ℝ v (sourceNormal e))
    (hfv : 0 < inner ℝ v (sourceNormal f))
    (hc : edgeComponent e = edgeComponent f) : e = f := by
  by_contra hne
  have hn := source_normals_opposite ht hf he hc hne
  rw [hn, inner_neg_right] at hev
  linarith

def semicircleSources {n : ℕ} (G : PennyGraph n) (v : Plane) : Finset (OrientedEdge G) :=
  Finset.univ.filter (fun e => SpineSource e ∧ 0 < inner ℝ v (sourceNormal e))

theorem semicircleSources_component_injOn {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (v : Plane) :
    Set.InjOn edgeComponent (semicircleSources G v : Set (OrientedEdge G)) := by
  intro e he f hf hc
  have he' := (Finset.mem_filter.mp he).2
  have hf' := (Finset.mem_filter.mp hf).2
  exact source_component_injective_in_open_semicircle ht v he'.1 hf'.1 he'.2 hf'.2 hc

theorem semicircleSources_card_le_tracks {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (v : Plane) :
    (semicircleSources G v).card ≤ Fintype.card (TrackComponent G) := by
  calc
    _ = ((semicircleSources G v).image edgeComponent).card :=
      (Finset.card_image_of_injOn (semicircleSources_component_injOn G ht v)).symm
    _ ≤ _ := Finset.card_le_univ _

theorem selected_semicircle_sources_card_image {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (v : Plane) (S : Finset (OrientedEdge G))
    (hS : S ⊆ semicircleSources G v) :
    (S.image edgeComponent).card = S.card := by
  apply Finset.card_image_of_injOn
  exact (semicircleSources_component_injOn G ht v).mono hS

theorem crossing_pair_bound_from_selected_sources {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (v : Plane) (A : Finset (TrackComponent G))
    (u w : TrackComponent G) (huw : ComponentCrosses u w)
    (S : Finset (OrientedEdge G)) (hS : S ⊆ semicircleSources G v)
    (hterm : ∀ e ∈ S, edgeComponent e ∈ A)
    (hmiss : ∀ e ∈ S, ¬ ComponentCrosses u (edgeComponent e) ∧
      ¬ ComponentCrosses w (edgeComponent e)) :
    (A.filter (ComponentCrosses u)).card + (A.filter (ComponentCrosses w)).card +
      S.card ≤ A.card := by
  let U := A.filter (ComponentCrosses u)
  let W := A.filter (ComponentCrosses w)
  let P := S.image edgeComponent
  have hUW : Disjoint U W := by
    apply Finset.disjoint_left.mpr
    intro c hcu hcw
    exact componentGraph_noTriple G ht u w c huw
      (Finset.mem_filter.mp hcw).2
      (((componentGraph G ht).adj_comm _ _).mp (Finset.mem_filter.mp hcu).2)
  have hUP : Disjoint U P := by
    apply Finset.disjoint_left.mpr
    intro c hcu hcp
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hcp
    exact (hmiss e he).1 (Finset.mem_filter.mp hcu).2
  have hWP : Disjoint W P := by
    apply Finset.disjoint_left.mpr
    intro c hcw hcp
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hcp
    exact (hmiss e he).2 (Finset.mem_filter.mp hcw).2
  have hsub : (U ∪ W) ∪ P ⊆ A := by
    apply Finset.union_subset
    · exact Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    · intro c hc
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hc
      exact hterm e he
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hUP, hWP⟩),
    Finset.card_union_of_disjoint hUW] at hcard
  have hp : P.card = S.card := selected_semicircle_sources_card_image G ht v S hS
  rwa [hp] at hcard

end Swanepoel
