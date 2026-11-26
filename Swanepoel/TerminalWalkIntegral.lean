module
public import Swanepoel.TerminalDisplacement
public import Swanepoel.JoinClosedFamilies
public import Swanepoel.FacePortCycles
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def PennyGraph.selectedWalkDisplacement {n : ℕ} (G : PennyGraph n)
    (A : Finset (TrackComponent G)) {S : Finset (ContactEdge G)}
    {a b : Fin n} (p : (G.contactGraph S).Walk a b) : Plane :=
  match p with
  | .nil => 0
  | .cons h q =>
    retainedDisplacement A ⟨(_, _),G.contactGraph_le S h⟩+G.selectedWalkDisplacement A q

theorem PennyGraph.selectedWalkDisplacement_append {n : ℕ} (G : PennyGraph n)
    (A : Finset (TrackComponent G)) {S : Finset (ContactEdge G)}
    {a b c : Fin n} (p : (G.contactGraph S).Walk a b) (q : (G.contactGraph S).Walk b c) :
    G.selectedWalkDisplacement A (p.append q)=
      G.selectedWalkDisplacement A p+G.selectedWalkDisplacement A q := by
  induction p with
  | nil => simp [PennyGraph.selectedWalkDisplacement]
  | cons h p ih => simp only [SimpleGraph.Walk.cons_append,PennyGraph.selectedWalkDisplacement,ih,add_assoc]

theorem PennyGraph.selectedWalkDisplacement_eq_endpoints {n : ℕ} (G : PennyGraph n)
    (A : Finset (TrackComponent G)) (S : Finset (ContactEdge G))
    (hretain : ∀ {a b : Fin n} (h : (G.contactGraph S).Adj a b),
      edgeComponent (⟨(a,b),G.contactGraph_le S h⟩ : OrientedEdge G)∈A)
    {a b : Fin n} (p : (G.contactGraph S).Walk a b) :
    G.selectedWalkDisplacement A p=G.point b-G.point a := by
  induction p with
  | nil => simp [PennyGraph.selectedWalkDisplacement]
  | @cons a c b h p ih =>
    rw [PennyGraph.selectedWalkDisplacement,retainedDisplacement_of_mem _ _ (hretain h),ih]
    change (G.point c-G.point a)+(G.point b-G.point c)=_
    abel

theorem PennyGraph.port_graph_edge_component_mem_family {n : ℕ} (G : PennyGraph n)
    (Y : Finset (PlaneFace G)) (F : PlaneFace G) (hF : F∈Y)
    {a b : Fin n} (h : (G.contactGraph (G.facePortEdges F)).Adj a b) :
    edgeComponent (⟨(a,b),G.contactGraph_le _ h⟩ : OrientedEdge G)∈G.familyTrackComponents Y := by
  obtain ⟨e,he,heq⟩ := G.port_graph_edge_has_source_orientation F h
  have heFamily : e∈G.familySourcePorts Y := by
    have hep := (Finset.mem_filter.mp he).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hep.1,hep.2 ▸ hF⟩
  have hc := edgeComponent_of_unordered_eq
    (⟨(a,b),G.contactGraph_le _ h⟩ : OrientedEdge G) e heq.symm
  rw [hc]
  exact Finset.mem_image.mpr ⟨e,heFamily,rfl⟩

theorem PennyGraph.family_port_walk_displacement {n : ℕ} (G : PennyGraph n)
    (Y : Finset (PlaneFace G)) (F : PlaneFace G) (hF : F∈Y)
    {a b : Fin n} (p : (G.contactGraph (G.facePortEdges F)).Walk a b) :
    G.selectedWalkDisplacement (G.familyTrackComponents Y) p=G.point b-G.point a :=
  G.selectedWalkDisplacement_eq_endpoints _ _
    (fun h => G.port_graph_edge_component_mem_family Y F hF h) p

theorem PennyGraph.family_port_closed_walk_displacement {n : ℕ} (G : PennyGraph n)
    (Y : Finset (PlaneFace G)) (F : PlaneFace G) (hF : F∈Y)
    {a : Fin n} (p : (G.contactGraph (G.facePortEdges F)).Walk a a) :
    G.selectedWalkDisplacement (G.familyTrackComponents Y) p=0 := by
  rw [G.family_port_walk_displacement Y F hF p,sub_self]

end Swanepoel
