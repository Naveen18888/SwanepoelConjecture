module
public import Swanepoel.TrackCardinality
public import Swanepoel.RhombusCenters
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def SpineTransition.rhombus {n : ℕ} {G : PennyGraph n}
    (p : SpineTransition G) : RhombusSet G := by
  refine ⟨stepCorners p.val.1 p.val.2,?_⟩
  obtain ⟨C,he,hf,_⟩ := p.property
  refine ⟨C,?_⟩
  have heq : p.val.1=C.edgeAB := Subtype.ext he
  have hfq : p.val.2=C.edgeDC := Subtype.ext hf
  rw [heq,hfq]
  exact C.stepCorners_eq.symm

theorem SpineTransition.center_eq {n : ℕ} {G : PennyGraph n}
    (p : SpineTransition G) :
    stepCenter p.val.1 p.val.2=p.rhombus.representative.center := by
  obtain ⟨C,he,hf,_⟩ := p.property
  have heq : p.val.1=C.edgeAB := Subtype.ext he
  have hfq : p.val.2=C.edgeDC := Subtype.ext hf
  have hc : C.corners=p.rhombus.representative.corners := by
    rw [p.rhombus.representative_corners]
    change C.corners=stepCorners p.val.1 p.val.2
    rw [heq,hfq]
    exact C.stepCorners_eq.symm
  rw [heq,hfq,C.stepCenter_eq]
  exact C.center_of_corners _ hc

def SpineTransition.reverse {n : ℕ} {G : PennyGraph n}
    (p : SpineTransition G) : SpineTransition G :=
  ⟨(reverseEdge p.val.2,reverseEdge p.val.1),p.property.reverse⟩

theorem SpineTransition.reverse_rhombus {n : ℕ} {G : PennyGraph n}
    (p : SpineTransition G) : p.reverse.rhombus=p.rhombus := by
  apply Subtype.ext
  exact stepCorners_reverseSwap p.val.1 p.val.2

theorem SpineTransition.reverse_component {n : ℕ} {G : PennyGraph n}
    (p : SpineTransition G) : edgeComponent p.reverse.val.1=edgeComponent p.val.1 :=
  (Swanepoel.reverse_component p.val.2).symm.trans
    (positive_path_component (.single p.property)).symm

theorem SpineTransition.reverse_ne {n : ℕ} {G : PennyGraph n}
    (p : SpineTransition G) : p≠p.reverse := by
  intro h
  have he : p.val.1=reverseEdge p.val.2 := congrArg (fun x : SpineTransition G => x.val.1) h
  exact spine_opposite_sources_ne (.single p.property) he

theorem transition_same_rhombus_component {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) (p q : SpineTransition G)
    (hr : p.rhombus=q.rhombus) (hc : edgeComponent p.val.1=edgeComponent q.val.1) :
    p=q ∨ p=q.reverse := by
  rcases component_step_centers ht p.property q.property hc with h | h | h
  · exact Or.inl (Subtype.ext (Prod.ext h.1 h.2))
  · exact Or.inr (Subtype.ext (Prod.ext h.1 h.2))
  · rw [p.center_eq,q.center_eq,hr,sub_self] at h
    simp [SharpNormal] at h

abbrev RhombusIncidence {n : ℕ} (G : PennyGraph n) :=
  {p : RhombusSet G × TrackComponent G //
    edgeComponent p.1.representative.edgeAB=p.2 ∨
    edgeComponent p.1.representative.edgeAD=p.2}

noncomputable instance {n : ℕ} (G : PennyGraph n) : Fintype (RhombusIncidence G) :=
  Fintype.ofFinite _

def transitionIncidence {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    (p : SpineTransition G) : RhombusIncidence G := by
  refine ⟨(p.rhombus,edgeComponent p.val.1),?_⟩
  have hc := p.rhombus.representative_corners
  change p.rhombus.representative.corners=stepCorners p.val.1 p.val.2 at hc
  have h1 : p.val.1.val.1 ∈ p.rhombus.representative.corners := by
    rw [hc]; simp [stepCorners]
  have h2 : p.val.1.val.2 ∈ p.rhombus.representative.corners := by
    rw [hc]; simp [stepCorners]
  rcases p.rhombus.representative.inside_component ht p.val.1 h1 h2 with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

theorem transitionIncidence_surjective {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree) :
    Function.Surjective (transitionIncidence ht) := by
  rintro ⟨⟨R,t⟩,hRt⟩
  obtain ⟨e,f,hpos,he,_,hcorners⟩ := R.representative.spineWitness ht t hRt
  let p : SpineTransition G := ⟨(e,f),hpos⟩
  refine ⟨p,?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact hcorners.trans R.representative_corners
  · exact he

theorem transitionIncidence_reverse {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    (p : SpineTransition G) : transitionIncidence ht p.reverse=transitionIncidence ht p := by
  apply Subtype.ext
  exact Prod.ext p.reverse_rhombus p.reverse_component

theorem transition_incidence_fiber_count {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    (I : RhombusIncidence G) :
    ((Finset.univ : Finset (SpineTransition G)).filter
      (fun p => transitionIncidence ht p=I)).card=2 := by
  classical
  obtain ⟨q,hq⟩ := transitionIncidence_surjective ht I
  have hset : ((Finset.univ : Finset (SpineTransition G)).filter
      (fun p => transitionIncidence ht p=I))={q,q.reverse} := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hp
      have hh := congrArg Subtype.val (hp.trans hq.symm)
      exact transition_same_rhombus_component ht p q (congrArg Prod.fst hh) (congrArg Prod.snd hh)
    · rintro (rfl | rfl)
      · exact hq
      · exact (transitionIncidence_reverse ht q).trans hq
  rw [hset,Finset.card_pair q.reverse_ne]

theorem rhombus_incidence_fiber_count {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    (R : RhombusSet G) :
    ((Finset.univ : Finset (RhombusIncidence G)).filter (fun I => I.val.1=R)).card=2 := by
  classical
  let A : RhombusIncidence G :=
    ⟨(R,edgeComponent R.representative.edgeAB),Or.inl rfl⟩
  let B : RhombusIncidence G :=
    ⟨(R,edgeComponent R.representative.edgeAD),Or.inr rfl⟩
  have hne : A≠B := by
    intro h
    exact R.representative.trackPair_ne ht (congrArg (fun I : RhombusIncidence G => I.val.2) h)
  have hset : ((Finset.univ : Finset (RhombusIncidence G)).filter
      (fun I => I.val.1=R))={A,B} := by
    ext I
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro h
      have hi := I.property
      rw [h] at hi
      rcases hi with hi | hi
      · exact Or.inl (Subtype.ext (Prod.ext h hi.symm))
      · exact Or.inr (Subtype.ext (Prod.ext h hi.symm))
    · rintro (rfl | rfl) <;> rfl
  rw [hset,Finset.card_pair hne]

theorem rhombus_incidence_count {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) :
    Fintype.card (RhombusIncidence G)=2*Fintype.card (RhombusSet G) := by
  have h := card_eq_mul_of_constant_fibers
    (Finset.univ : Finset (RhombusIncidence G)) (fun I => I.val.1) 2
    (rhombus_incidence_fiber_count ht)
  simpa only [Finset.card_univ,Nat.mul_comm] using h

theorem rhombus_transition_count {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) :
    Fintype.card (SpineTransition G)=4*Fintype.card (RhombusSet G) := by
  have h := card_eq_mul_of_constant_fibers
    (Finset.univ : Finset (SpineTransition G)) (transitionIncidence ht) 2
    (transition_incidence_fiber_count ht)
  simp only [Finset.card_univ,rhombus_incidence_count G ht] at h
  omega

theorem geometric_track_identity {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) :
    (G.edgeCount : ℤ)-Fintype.card (TrackComponent G)=
      2*Fintype.card (RhombusSet G) := by
  have h := transition_track_count G ht
  rw [rhombus_transition_count G ht] at h
  omega

end Swanepoel
