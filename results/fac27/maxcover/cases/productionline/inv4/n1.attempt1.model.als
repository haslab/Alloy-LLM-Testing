abstract sig Atom {}
sig WorkstationAtom, WorkerAtom, ProductAtom extends Atom {}
abstract sig Formula {}
one sig Oracle extends Formula {}
sig detected in Formula {}
sig Instance {
    valid : set Formula,
    Workstation : set WorkstationAtom,
    begin : set WorkstationAtom,
    end : set WorkstationAtom,
    Worker : set WorkerAtom,
    Human : set WorkerAtom,
    Robot : set WorkerAtom,
    Product : set ProductAtom,
    Material : set ProductAtom,
    Component : set ProductAtom,
    Dangerous : set ProductAtom,
    workers : WorkstationAtom -> WorkerAtom,
    succ : WorkstationAtom -> WorkstationAtom,
    parts : ProductAtom -> ProductAtom,
    workstation : ProductAtom -> WorkstationAtom
} {
    workers in Workstation -> Worker
    succ in Workstation -> Workstation
    parts in Product -> Product
    workstation in Component -> Workstation
    one begin
    one end
    begin + end in Workstation
    Human + Robot in Worker
    no Human & Robot
    Product = Material + Component
    no Material & Component
    Dangerous in Product
    // Earlier requirement 0, required in every Instance.
{
	// Workers are either human or robots
 all w: Worker | w in Human or w in Robot
}
    // Earlier requirement 1, required in every Instance.
{
	// Every workstation has workers and every worker works in one workstation
	all ws: Workstation | some ws.workers
  	all w: Worker | one ws: Workstation | w in ws.workers
}
    // Earlier requirement 2, required in every Instance.
{
	// Every component is assembled in one workstation
	all c: Component | one c.workstation
}
    Oracle in valid iff {
	// Components must have parts and materials have no parts
	all c: Component | some c.parts
    all m: Material | no m.parts
}
    S1 in valid iff {
	// Components must have parts and materials have no parts

}
    S2 in valid iff {
  // Components must have parts and materials have no parts
  all c: Component, m: Material | some c.parts and no m.parts
}
    S3 in valid iff {
	// Components must have parts and materials have no parts
  	(all c:Component | some c.parts ) and (all p:Product | no p.parts )

}
    S4 in valid iff {
	// Components must have parts and materials have no parts
	(some Component.parts) and (no Material.parts)
}
    S5 in valid iff {
	// Components must have parts and materials have no parts
	all c: Component | some c.parts and all m: Material | no m.parts
}
    S6 in valid iff {
	// Components must have parts and materials have no parts
	all o: Component | some o.parts
}
    S7 in valid iff {
	// Components must have parts and materials have no parts
	all p:Product | p in Material implies not one p.parts
}
    S8 in valid iff {
	// Components must have parts and materials have no parts
	all p:Product | some p.parts implies p in Component 

}
    S9 in valid iff {
	// Components must have parts and materials have no parts
	all p:Product | p.parts in (Component-Material)

}
    S10 in valid iff {
	// Components must have parts and materials have no parts
	all p:Product | p.parts in Component and p.parts not in Material

}
    S11 in valid iff {
	// Components must have parts and materials have no parts
	no p:Product | p.parts in Material

}
    S12 in valid iff {
	// Components must have parts and materials have no parts
  	all c : Component | some(c.parts)
	some(Component <: parts) and no (Material <: parts)
}
    S13 in valid iff {
	// Components must have parts and materials have no parts
	all c: Component | c.parts != none and all m: Material | m in Product - Product.parts
}
    S14 in valid iff {
	// Components must have parts and materials have no parts
	all c:Component | some parts 
  	all m:Material | no parts
}
    S15 in valid iff {
	// Components must have parts and materials have no parts
	all c : Component | c.parts != none
  	all c : Material | c.parts != none
}
    S16 in valid iff {
	// Components must have parts and materials have no parts
  	all c: (Material + Component) | (c in Material) implies some c.parts else no c.parts

}
    S17 in valid iff {
	// Components must have parts and materials have no parts
	some (Product & Component - Dangerous).parts and no (Product & Material - Dangerous).parts 
}
    S18 in valid iff {
	// Components must have parts and materials have no parts
	all p: Material | p.parts not in Product
  	all p: Component | p.parts in Product
}
    S19 in valid iff {
	// Components must have parts and materials have no parts
	all c:Component | some p:c.parts | p in Product
  	all m:Material | one p:m.parts |p not in Product
}
    S20 in valid iff {
	// Components must have parts and materials have no parts
	all c : Component, m : Material | some p : Product | c in p.parts and m not in p.parts 
}
    S21 in valid iff {
	// Components must have parts and materials have no parts
	all c : Component, m : Material | some p : Product | c in parts.p and m in parts.p 
}
    S22 in valid iff {
	// Components must have parts and materials have no parts
	all c: Component, m:Material | some p:Product | p in c.parts and p not in m.parts
}
    S23 in valid iff {
	// Components must have parts and materials have no parts
	all c: Component, m: Material | c in c.parts and m not in m.parts
}
    S24 in valid iff {
	// Components must have parts and materials have no parts
	all c : Component | all m : Material | one c.parts and no m.parts		
}
    S25 in valid iff {
	// Components must have parts and materials have no parts
  
	all c : Component, m : Material, p : Product | one p2 : Product | c not in c.parts and c not in parts.c and p not in m.parts and p2 in c.parts
}
    S26 in valid iff {
  all c : Component | one p : Product | all m : Material | p in c.parts and p not in m.parts
	// Components must have parts and materials have no parts

}
    S27 in valid iff {
  all c : Component | one p : Product | all m : Material | p in c.parts and p not in m.parts and c not in c.parts and m not in m.parts
	// Components must have parts and materials have no parts

}
    S28 in valid iff {
  all p : Product | (p not in p.parts and p not in parts.p) and #(p.parts)>0 implies p in Component 
	// Components must have parts and materials have no parts

}
    S29 in valid iff {
	// Components must have parts and materials have no parts
 	//all p:Product | p not in p.^parts
  	all c: Component | c.((^(parts)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) in (Product - c)
  	//all m: Material  | m.parts not in (Product)  	
}
    S30 in valid iff {
	// Components must have parts and materials have no parts
  
	//all p : Product | #(p.parts)>0 implies p in Component else p in Material
  
  	all c : Component | some Component.parts
  	all m : Material | no Material.parts
}
    S31 in valid iff {
	// Components must have parts and materials have no parts
  	all c : Product | some p: c.parts | p in Product implies c in Component
  	all prod:Product | one p:prod.parts | p not in Product implies prod in Material
}
    S32 in valid iff {
	// Components must have parts and materials have no parts
	all c : Component, m : Material | some c.parts
    all m : Material | no m.parts
}
    S33 in valid iff {
	// Components must have parts and materials have no parts
	all p : Product | p in Component and some p.parts
  	all m : Product | m in Material and no m.parts
}
    S34 in valid iff {
	// Components must have parts and materials have no parts
	all c : Component , m : Material | #c.parts > 0 and m.parts = 0
}
    S35 in valid iff {
	// Components must have parts and materials have no parts
  
	// all components must have parts (itself included)
  	// all materials must have no parts (itself included)
  	all c: Component | c.parts in (Product - c)
  	all m:Material | m.parts not in (Product)
  	
}
    S36 in valid iff {
	// Components must have parts and materials have no parts
  	all c: Component | c.parts in (Product - c)
  	all m:Material | m.parts not in (Product - m)  	
}
    S37 in valid iff {
	// Components must have parts and materials have no parts
  	all c: Component | c.^parts in (Product - c)
  	all m: Material  | m.parts not in (Product)  	
}
    S38 in valid iff {
	// Components must have parts and materials have no parts
 	all p:Product | p not in p.^parts
  	//all c: Component | c.^parts in (Product - c)
  	//all m: Material  | m.parts not in (Product)  	
}
    S39 in valid iff {
	// Components must have parts and materials have no parts
 	//all p:Product | p not in p.^parts
  	all c: Component | c.^parts in (Product - c)
  	//all m: Material  | m.parts not in (Product)  	
}
    S40 in valid iff {
	// Components must have parts and materials have no parts
 	all p:Product | p.parts in (Product-p)
  	//all c: Component | c.*parts in (Product - c)
  	//all m: Material  | m.parts not in (Product)  	
}
    S41 in valid iff {
	// Components must have parts and materials have no parts
  	#(Component & Product.parts) != 0
  	#(Material & Product.parts) != 0

}
    S42 in valid iff {
	// Components must have parts and materials have no parts
  	#(Component & Product.parts) != 0
  	#(Material & Product.parts) = 0

}
    S43 in valid iff {
	// Components must have parts and materials have no parts
  all c : Component | some parts.c
  
  all m : Material | no parts.m

}
    S44 in valid iff {
	// Components must have parts and materials have no parts
  	no (((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden) & parts) and parts in (Component -> set Product)

}
    S45 in valid iff {
	// Components must have parts and materials have no parts
  	no (((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden) & parts) and parts in (Component -> some Product)

}
    S46 in valid iff {
	// Components must have parts and materials have no parts
	all c : Component | all m : Material | some c.parts - c and no m.parts		
}
    S47 in valid iff {
	// Components must have parts and materials have no parts
	all c : Component | all m : Material | some c.parts - c and no m.parts - m		
}
    S48 in valid iff {
	// Components must have parts and materials have no parts
  	all c : Component, p : Product | p.parts in c
  	all m : Material, p : Product | m not in p.parts

}
    S49 in valid iff {
	// Components must have parts and materials have no parts
	//all m : Material | all c : Component | none m.parts | some c.parts
    Product not in Material.parts
  	Product in Component.parts
}
    S50 in valid iff {
	// Components must have parts and materials have no parts
	all c:Component, m:Material | some p:Product | p in p.parts and p not in m.parts
}
    S51 in valid iff {
	// Components must have parts and materials have no parts
	all c:Component, m:Material | some p:Product | p in p.parts and p not in m.parts
  	all c:Component | some p: Product | c.parts = p
}
    S52 in valid iff {
	// Components must have parts and materials have no parts
	all c:Component, m:Material | some p:Product | p in p.parts and p not in m.parts
  	all c:Component | some p: Product | p in c.parts
}
    S53 in valid iff {
	// Components must have parts and materials have no parts
  	all c:Component | some p: Product | p in c.parts
  	all c:Material | some p: Product | p not in c.parts
}
    S54 in valid iff {
	// Components must have parts and materials have no parts
	all c: Component | some c.parts
  	all m: Material | one m.parts
}
    S55 in valid iff {
	// Components must have parts and materials have no parts
	all p : Product, m : Material, c : Component | p in c.parts and p not in m.parts
}
    S56 in valid iff {
	// Components must have parts and materials have no parts
  all c: Component, m: Material | #c.parts>0 and #m.parts =0 and c not in c.parts

}
    S57 in valid iff {
	// Components must have parts and materials have no parts
	all p: Product, c: Component, m: Material |
  		some c.parts implies no m.parts
  		
}
    S58 in valid iff {
	// Components must have parts and materials have no parts
  
  all c : Component | c-> c in parts
  all m : Material | no m.parts

}
    S59 in valid iff {
	// Components must have parts and materials have no parts
  
  all c : Component | (some c1 : Component | c-> c1 in parts)
  all m : Material | no m.parts

}
    S60 in valid iff {
	// Components must have parts and materials have no parts
  
  all c : Component | (some c : Component | c-> c in parts)
  all m : Material | no m.parts

}
    S61 in valid iff {
	// Components must have parts and materials have no parts
	all p: Product | some p2: Product | p != p2 and (p in Component implies p2 in p.parts) or (p in Material implies p2 not in p.parts)
}
    S62 in valid iff {
	// Components must have parts and materials have no parts
	all p: Product | some p2: Product | p in Material implies p2 not in p.parts
}
    S63 in valid iff {
	// Components must have parts and materials have no parts
	all disj p, p2 : Product | p in Material implies p2 not in p.parts
}
    S64 in valid iff {
	// Components must have parts and materials have no parts
	//all c: Component | some c.parts
  	 //all m: Material | no m.parts
  
  	all c: Component, p: Product | p in c.parts
  	 all m: Material, p: Product | not p in m.parts
}
    S65 in valid iff {
	// Components must have parts and materials have no parts
	all c : Component, m : Material | lone c.parts and no m.parts
}
    S66 in valid iff {
	// Components must have parts and materials have no parts
	all p: Product| (p = Component implies p.parts != none) and
  	(p = Material implies p.parts = none)
}
    S67 in valid iff {
	// Components must have parts and materials have no parts
	all p: Product| (p = Component implies p.parts != none and p not in p.parts) and
  	(p = Material implies p.parts = none)
}
    S68 in valid iff {
	// Components must have parts and materials have no parts
  no parts.Material
  all c:Component | some c.parts

}
    S69 in valid iff {
	// Components must have parts and materials have no parts
  all c : Component, m : Material | some c.parts

}
    S70 in valid iff {
	// Components must have parts and materials have no parts
	all c: Component | all m: Material | c in c.parts and no m.parts
}
    S71 in valid iff {
	// Components must have parts and materials have no parts
	all c : Component, m : Material | #(c.parts) >= 0  and no m.parts
}
    S72 in valid iff {
	// Components must have parts and materials have no parts
  some Component.parts and no Material.parts and all c:Component| c not in c.parts 

}
    S73 in valid iff {
	// Components must have parts
  all c: Component | lone(c.parts)
  // and materials have no parts
  all m: Material | no m.parts 
}
    S74 in valid iff {
	// Components must have parts and materials have no parts
	all c:Component, m:Material | c.parts != none and m.parts = none
  	all c:Component | c not in c.parts
}
    S75 in valid iff {
	// Components must have parts and materials have no parts
	all p: Material |
  		p.parts = none 
  
  	all p: Component |
  		some (p.parts - p)
  
  	Product = Material + Component
  		
}
    S76 in valid iff {
	// Components must have parts and materials have no parts
	all c: Component, p: Product | c in p.parts
  	 all m: Material, p: Product | not m in p.parts
}
    S77 in valid iff {
	// Components must have parts and materials have no parts
	//all c: Component | some c.parts
  	 //all m: Material | no m.parts
  
  	all c: Component, p: Product | c in p implies c in p.parts
  	 all m: Material, p: Product | m in p implies m not in p.parts
}
    S78 in valid iff {
	// Components must have parts and materials have no parts
	all c:Component, x: Workstation, p:Product | c in workstation.x implies (c in parts.p and Material not in parts.p)
}
    S79 in valid iff {
	// Components must have parts and materials have no parts
	Component.parts = Component
  	no (Material.parts)

}
    S80 in valid iff {
	// Components must have parts and materials have no parts
	all c:Component | some p: Product | c in p.parts
}
    S81 in valid iff {
	// Components must have parts and materials have no parts
  	Product in Component.parts 
	//all c: Component | some c.parts
  	no (Material.parts)

}
    S82 in valid iff {
	// Components must have parts and materials have no parts
	parts in Product one -> some Component
}
    S83 in valid iff {
	// Components must have parts and materials have no parts
  	// all c: Component | some c.parts
  	// all m : Material | no m.parts
  
	(parts in Product some -> Component) and
  	not (parts in Product ->  Material) 
}
    S84 in valid iff {
	// Components must have parts and materials have no parts
  	Material not in Product.parts
  	Component in Product.parts

}
    S85 in valid iff {
	// Components must have parts and materials have no parts
  	Material not in parts.Product
  	Component in parts.Product

}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72, S73, S74, S75, S76, S77, S78, S79, S80, S81, S82, S83, S84, S85 extends Formula {}

run {
    #valid.Oracle = 1
    #(Instance - valid.Oracle) = 1
    detected = { f : Formula - Oracle | valid.f != valid.Oracle }
    maxsome detected
} for exactly 12 Atom, exactly 4 WorkstationAtom, exactly 4 WorkerAtom, exactly 4 ProductAtom,
       exactly 2 Instance, 6 Int
