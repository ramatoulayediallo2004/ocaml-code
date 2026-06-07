(*******************************************************************) 
(* Langages de Programmation: IFT-3000                             *)
(* TP1 - Résolution de labyrinthe                                  *)
(*******************************************************************) 
(* Étudiant(e) :                                                   *)
(* NOM : _DIALLO PRÉNOM : ___RAMATOULAYE *)
(* MATRICULE : _________537193274 PROGRAMME : INFORMATIQUE *)
(*******************************************************************) 

open List

(*******************************************************************)
(* Déclarations d'exceptions et de types                           *)
(*******************************************************************)

exception Non_Implante  of string
exception Labyrinthe_invalide of string

(** Couleur d'un joueur. [Aucun] est retourné quand aucun joueur ne gagne. *)
type couleur = Rouge | Vert | Bleu | Jaune | Aucun

(** Une porte relie la pièce qui la contient à une pièce destination,
    et ne peut être franchie que par le joueur de la couleur correspondante. *)
type porte = { couleur_porte : couleur; destination : string }

(** Une pièce identifiée par son nom, dotée d'une liste de portes sortantes. *)
type piece = { nom : string; portes : porte list }

(** Un labyrinthe : liste de pièces + nom de la pièce de départ + nom de l'arrivée. *)
type labyrinthe = { pieces : piece list; depart : string; arrivee : string }

(*******************************************************************)
(* Fonctions fournies — manipulation de listes                     *)
(*******************************************************************)

(** [appartient e l] retourne [true] si [e] est présent dans [l]. *)
let appartient e l = exists (fun x -> x = e) l

(** [enlever e l] retourne [l] privée de toutes les occurrences de [e]. *)
let enlever e l =
  let (_, l') = partition (fun x -> x = e) l in l'

(** [remplacer e e' l] remplace chaque occurrence de [e] par [e'] dans [l]. *)
let remplacer e e' l =
  map (fun x -> if x = e then e' else x) l

(** [union_liste l1 l2] retourne l'union de [l1] et [l2] sans doublons. *)
let rec union_liste l1 l2 = match l2 with
  | []     -> l1
  | x :: r -> if appartient x l1 then union_liste l1 r
              else union_liste (l1 @ [x]) r

(*******************************************************************)
(* Fonctions fournies — manipulation du labyrinthe                 *)
(* (chargement depuis les fichiers .txt)                           *)
(*******************************************************************)

(** Construit le nom d'une pièce à partir de ses coordonnées (i, j). *)
let nom_de_coords i j = string_of_int i ^ "," ^ string_of_int j

(** Retourne le caractère à la position [i] dans [s], ou [' '] si hors bornes. *)
let char_at s i = if i >= 0 && i < String.length s then s.[i] else ' '

(** Lit toutes les lignes d'un canal jusqu'à [End_of_file]. *)
let lire_lignes canal =
  let rec aux acc =
    match (try Some (input_line canal) with End_of_file -> None) with
    | None       -> rev acc
    | Some ligne -> aux (ligne :: acc)
  in aux []

(** Initialise une liste de pièces vides pour toutes les coordonnées (i, j). *)
let init_pieces nb_cols nb_rangs =
  let rec aux_j i j acc =
    if j >= nb_rangs then acc
    else aux_j i (j+1) (acc @ [{ nom = nom_de_coords i j; portes = [] }])
  in
  let rec aux_i i acc =
    if i >= nb_cols then acc
    else
      let nouvelles = aux_j i 0 [] in
      let acc' = fold_left (fun a p ->
        if appartient p.nom (map (fun q -> q.nom) a) then a else a @ [p]
      ) acc nouvelles in
      aux_i (i+1) acc'
  in
  aux_i 0 []

(** Ajoute une porte de couleur [c] de la pièce [nom1] vers la pièce [nom2]. *)
let ajoute_passage_dans_pieces c nom1 nom2 pieces =
  map (fun p ->
    if p.nom = nom1 then
      { p with portes = p.portes @ [{ couleur_porte = c; destination = nom2 }] }
    else p
  ) pieces

(** Extrait le départ/arrivée depuis la première ligne de données du fichier. *)
let parse_depart_arrivee_ligne0 ligne nb_cols =
  let rec aux i dep arr =
    if i >= nb_cols then (dep, arr)
    else
      let c = char_at ligne (i * 4 + 1) in
      let dep' = if c='D' || c='d' then Some (nom_de_coords i 0) else dep in
      let arr' = if c='F' || c='f' || c='A' || c='a'
                 then Some (nom_de_coords i 0) else arr in
      aux (i+1) dep' arr'
  in aux 0 None None

(** Met à jour départ/arrivée depuis une ligne intermédiaire du fichier. *)
let update_depart_arrivee ligne j nb_cols nb_rangs dep arr =
  let debut_i = if j = nb_rangs-1 && j land 1 = 1 then 1 else 0 in
  let rec aux i d a =
    if i >= nb_cols then (d, a)
    else
      let (d', a') =
        if j land 1 = 1 then
          let c = char_at ligne (i*4+1) in
          let d2 = if j < nb_rangs-1 && (c='D'||c='d')
                   then Some (nom_de_coords i (j+1)) else d in
          let a2 = if j < nb_rangs-1 && (c='F'||c='f'||c='A'||c='a')
                   then Some (nom_de_coords i (j+1)) else a in
          (d2, a2)
        else
          let c = char_at ligne (i*4+3) in
          let d2 = if j < nb_rangs-1 && (c='D'||c='d')
                   then Some (nom_de_coords i (j+1)) else d in
          let a2 = if j < nb_rangs-1 && (c='F'||c='f'||c='A'||c='a')
                   then Some (nom_de_coords i (j+1)) else a in
          (d2, a2)
      in aux (i+1) d' a'
  in aux debut_i dep arr

(** Parse les passages d'une ligne de la grille et les ajoute aux pièces. *)
let parse_passages_ligne couleur ligne j nb_cols nb_rangs pieces =
  let debut_i = if j = nb_rangs-1 && j land 1 = 1 then 1 else 0 in
  let rec aux i pcs =
    if i >= nb_cols then pcs
    else
      let pcs' =
        if j land 1 = 1 then
          let p1 = if j < nb_rangs-2 && char_at ligne (i*4+3) = ' '
                   then ajoute_passage_dans_pieces couleur
                          (nom_de_coords i j) (nom_de_coords i (j+2)) pcs
                   else pcs in
          let p2 = if j < nb_rangs-1 && char_at ligne (i*4+2) = ' '
                   then ajoute_passage_dans_pieces couleur
                          (nom_de_coords i j) (nom_de_coords i (j+1)) p1
                   else p1 in
          if j < nb_rangs-1 && char_at ligne (i*4+0) = ' '
          then ajoute_passage_dans_pieces couleur
                 (nom_de_coords (i-1) j) (nom_de_coords i (j+1)) p2
          else p2
        else
          let p1 = if j < nb_rangs-1 && char_at ligne (i*4+0) = ' '
                   then ajoute_passage_dans_pieces couleur
                          (nom_de_coords (i-1) (j+1)) (nom_de_coords i j) pcs
                   else pcs in
          let p2 = if j < nb_rangs-2 && char_at ligne (i*4+1) = ' '
                   then ajoute_passage_dans_pieces couleur
                          (nom_de_coords i j) (nom_de_coords i (j+2)) p1
                   else p1 in
          if j < nb_rangs-1 && char_at ligne (i*4+2) = ' '
          then ajoute_passage_dans_pieces couleur
                 (nom_de_coords i j) (nom_de_coords i (j+1)) p2
          else p2
      in aux (i+1) pcs'
  in aux debut_i pieces

(** Charge un labyrinthe pour une couleur depuis une liste de lignes et le
    fusionne avec un labyrinthe existant [lab_opt]. *)
let charge_labyrinthe_depuis_lignes couleur lignes lab_opt =
  match lignes with
  | [] -> raise (Labyrinthe_invalide "Fichier vide")
  | entete :: reste ->
    let parts = filter (fun s -> s <> "")
                  (String.split_on_char ' ' (String.trim entete)) in
    let (nb_cols, nb_rangs) = match parts with
      | [c; r] -> (int_of_string c, int_of_string r)
      | _ -> raise (Labyrinthe_invalide "En-tête invalide")
    in
    let data_lines = match reste with
      | _ :: _ :: suite -> suite
      | _ -> raise (Labyrinthe_invalide "Format invalide")
    in
    let ligne0 = match reste with _ :: l :: _ -> l | _ -> "" in
    let pieces_base = match lab_opt with
      | None ->
        init_pieces nb_cols nb_rangs
      | Some lab ->
        fold_left (fun acc p ->
          if appartient p.nom (map (fun q -> q.nom) acc) then acc
          else acc @ [p]
        ) lab.pieces (init_pieces nb_cols nb_rangs)
    in
    let (dep0, arr0) = parse_depart_arrivee_ligne0 ligne0 nb_cols in
    let rec parcours j lignes_rest pcs dep arr =
      match lignes_rest with
      | [] -> (pcs, dep, arr)
      | ligne :: suite ->
        let pcs' = parse_passages_ligne couleur ligne j nb_cols nb_rangs pcs in
        let (dep', arr') = update_depart_arrivee ligne j nb_cols nb_rangs dep arr in
        parcours (j+1) suite pcs' dep' arr'
    in
    let (pieces_fin, dep_fin, arr_fin) = parcours 0 data_lines pieces_base dep0 arr0 in
    let depart_nom = match dep_fin with
      | Some n -> n
      | None -> (match lab_opt with
                 | Some lab -> lab.depart
                 | None -> raise (Labyrinthe_invalide "Pas de départ trouvé"))
    in
    let arrivee_nom = match arr_fin with
      | Some n -> n
      | None -> (match lab_opt with
                 | Some lab -> lab.arrivee
                 | None -> raise (Labyrinthe_invalide "Pas d'arrivée trouvée"))
    in
    { pieces = pieces_fin; depart = depart_nom; arrivee = arrivee_nom }

(** Charge un labyrinthe depuis un fichier pour une couleur donnée et le
    fusionne avec le labyrinthe optionnel [lab_opt]. *)
let charge_labyrinthe_fichier couleur chemin lab_opt =
  let canal = open_in chemin in
  let lignes = lire_lignes canal in
  close_in canal;
  charge_labyrinthe_depuis_lignes couleur lignes lab_opt

(*******************************************************************)
(* Fonctions à implémenter                                         *)
(* ----------------------------------------------------------------*)
(* Remplacez chaque raise (Non_Implante ...) par votre code.       *)
(*******************************************************************)

(* Fonction retournant la pièce de nom [nom] dans [lab].           *)
(* Lève Labyrinthe_invalide si la pièce est introuvable.           *)
(* type : string -> labyrinthe -> piece                            *)
(* -- À IMPLÉMENTER -------------------------------------------- *)

let trouve_piece nom lab =
  try find (fun p -> p.nom = nom) lab.pieces
  with Not_found -> raise (Labyrinthe_invalide ("Pièce " ^ nom ^ " introuvable"))

(* Fonction ajoutant la pièce [p] dans [lab].                      *)
(* Si une pièce de même nom existe déjà, retourner lab inchangé.   *)
(* type : piece -> labyrinthe -> labyrinthe                        *)
(* -- À IMPLÉMENTER -------------------------------------------- *)

let ajoute_piece p lab =
  if appartient p.nom (map (fun q -> q.nom) lab.pieces) then lab
  else { lab with pieces = lab.pieces @ [p] }

(* Fonction ajoutant [porte] à la pièce [nom_piece] dans [lab].    *)
(* Lève Labyrinthe_invalide si la pièce est introuvable.           *)
(* type : porte -> string -> labyrinthe -> labyrinthe              *)
(* -- À IMPLÉMENTER -------------------------------------------- *)

let ajoute_porte porte nom_piece lab = 
   let _ = trouve_piece nom_piece lab in
  let nouvelle_pieces = map (fun p ->
    if p.nom = nom_piece then
      { p with portes = p.portes @ [porte] }
    else p
  ) lab.pieces in
  { lab with pieces = nouvelle_pieces }

(* Parcours en largeur (BFS) depuis lab.depart vers lab.arrivee    *)
(* en utilisant une file FIFO (module Queue).                      *)
(* Ne parcourt que les portes de la couleur [joueur].              *)
(* Retourne la distance minimale, ou -1 si impossible.             *)
(* type : labyrinthe -> couleur -> int                             *)
(* -- À IMPLÉMENTER -------------------------------------------- *)

let parcours_en_largeur lab joueur =
    let q = Queue.create()in
  Queue.add (lab.depart,0) q ;
  let liste_visitee = [lab.depart] in 
  let rec bfs_visite liste_visitee  = if Queue.is_empty q then -1 else let (nom_piece,dist)= Queue.take q in
      if nom_piece = lab.arrivee then dist else let p = trouve_piece nom_piece lab in
        let portes_sortantes = filter(fun p -> p.couleur_porte = joueur)p.portes in
        let portes_inverse = filter (fun piece -> exists (fun porte -> porte.couleur_porte = joueur 
                                                                       && porte.destination = nom_piece) piece.portes) lab.pieces in 
        let voisins_sortants=  map(fun porte->porte.destination ) portes_sortantes in 
        let voisins_inverses= map  (fun piece ->piece.nom)portes_inverse in 
        let voisin = union_liste voisins_sortants voisins_inverses in
        let nouveaux = filter (fun v -> not(appartient v liste_visitee))voisin in
        iter (fun v->Queue.add(v,dist+1)q)nouveaux ; 
        let nouvelle_liste = union_liste liste_visitee nouveaux in
        bfs_visite nouvelle_liste
  in bfs_visite liste_visitee
  

(* Résout le labyrinthe pour [joueur] en appelant parcours_en_largeur.  *)
(* Lève Labyrinthe_invalide si joueur = Aucun.                          *)
(* type : labyrinthe -> couleur -> int                                  *)
(* -- À IMPLÉMENTER -------------------------------------------- *)

let solutionner lab joueur =
  if joueur = Aucun then raise (Labyrinthe_invalide "Aucun joueur ne peut résoudre le labyrinthe")
  else parcours_en_largeur lab joueur

(* Retourne la couleur du joueur gagnant (le moins de déplacements).    *)
(* Priorité en cas d'égalité : Rouge > Vert > Bleu > Jaune.            *)
(* Retourne Aucun si aucun joueur ne peut résoudre le labyrinthe.       *)
(* type : labyrinthe -> couleur                                         *)
(* -- À IMPLÉMENTER -------------------------------------------- *)

let trouve_gagnant lab =
  let score_rouge = solutionner lab Rouge in
  let score_vert = solutionner lab Vert in
  let score_bleu = solutionner lab Bleu in
  let score_jaune = solutionner lab Jaune in let   helper a b  = if a = -1 then b else if  b = -1 then a else min a b in 
  let meilleur = helper score_rouge (helper score_vert (helper score_bleu score_jaune)) in
   if meilleur = -1 then Aucun  else if meilleur = score_rouge then Rouge  
  else if meilleur = score_vert then Vert else if meilleur = score_bleu then Bleu else Jaune

(** [string_of_couleur c] retourne la représentation textuelle de [c]. *)

  let string_of_couleur = function
  | Rouge -> "Rouge"
  | Vert  -> "Vert"
  | Bleu  -> "Bleu"
  | Jaune -> "Jaune"
  | Aucun -> "Aucun"


(* Affiche le score de chaque joueur et le joueur gagnant.         *)
(* type : labyrinthe -> unit                                       *)
(* -- À IMPLÉMENTER -------------------------------------------- *)

let afficher_resultats lab =
  let score_rouge = solutionner lab Rouge in
  let score_vert = solutionner lab Vert in
  let score_bleu = solutionner lab Bleu in
  let score_jaune = solutionner lab Jaune in
  if score_rouge = -1 then print_string "Le joueur Rouge ne peut pas solutionner le labyrinthe.\n"
  else print_string ("Le joueur Rouge peut solutionner le labyrinthe en : " ^ string_of_int score_rouge ^ " déplacements\n");
  if score_vert = -1 then print_string "Le joueur Vert ne peut pas solutionner le labyrinthe.\n"
  else print_string ("Le joueur Vert peut solutionner le labyrinthe en: " ^ string_of_int score_vert ^ " déplacements\n");
  if score_bleu = -1 then print_string "Le joueur Bleu ne peut pas solutionner le labyrinthe.\n"
  else print_string ("Le joueur Bleu peut solutionner le labyrinthe en : " ^ string_of_int score_bleu ^ " déplacements\n");
  if score_jaune = -1 then print_string "Le joueur Jaune ne peut pas solutionner le labyrinthe.\n"
  else print_string ("Le joueur Jaune peut solutionner le labyrinthe en :  " ^ string_of_int score_jaune ^ " déplacements\n");
  let gagnant = trouve_gagnant lab in
  if gagnant = Aucun then print_string "Aucun joueur ne peut résoudre le labyrinthe.\n"
  else print_string ("Le joueur gagnant: " ^ string_of_couleur gagnant ^ "\n")


