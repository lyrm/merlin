open Std
open Parsetree
open Parsebrowse_raw

type node = Parsebrowse_raw.node
type t = node list

let fold_node = Parsebrowse_raw.fold_node

let approximate_loc get_loc node =
  let loc = get_loc Location.none node in
  if loc == Location.none then
    let rec aux node acc =
      let loc = get_loc Location.none node in
      if loc != Location.none then Location_aux.union loc acc
      else fold_node aux node acc
    in
    aux node Location.none
  else loc

let node_loc node = approximate_loc Parsebrowse_raw.node_real_loc node

let node_merlin_loc node = approximate_loc Parsebrowse_raw.node_merlin_loc node

let is_hidden node = Parsebrowse_raw.has_attr ~name:"merlin.hide" node

let is_focus node = Parsebrowse_raw.has_attr ~name:"merlin.focus" node

let leaf_node = List.hd

let select_leafs pos (root : t) =
  let branches = ref [] in
  let rec select_child (branch : t) node has_selected =
    let loc = node_merlin_loc node in
    if Location_aux.compare_pos pos loc = 0 && not (is_hidden node) then (
      traverse (node :: branch);
      true)
    else has_selected
  and traverse (branch : t) =
    let node = leaf_node branch in
    if is_focus node then (
      branches := [];
      let has_leaves = fold_node (select_child branch) node false in
      if not has_leaves then branches := [ branch ];
      raise Exit)
    else if not (is_hidden node) then
      let has_leaves = fold_node (select_child branch) node false in
      if not has_leaves then branches := branch :: !branches
  in
  (try traverse root with Exit -> ());
  !branches

module Tie_breaker = struct
  type tie_break = Prefer_first | Prefer_second
  type t = node -> node -> tie_break option

  let prefer_expression node1 node2 : tie_break option =
    match (node1, node2) with
    | Expression _, Expression _ -> None
    | Expression _, _ -> Some Prefer_first
    | _, Expression _ -> Some Prefer_second
    | _ -> None
end

let compare_locations ?tie_break pos l1 l2 =
  let t2_first = 1 in
  let t1_first = -1 in
  match (Location_aux.compare_pos pos l1, Location_aux.compare_pos pos l2) with
  (* Cursor inside both locations: favor non-ghost, fallback to user-provided
     tie-break, fallback to being closer to the end *)
  | 0, 0 ->
    begin match (tie_break, l1.Location.loc_ghost, l2.Location.loc_ghost) with
    | _, true, false -> 1
    | _, false, true -> -1
    | Some Tie_breaker.Prefer_first, _, _ -> t1_first
    | Some Prefer_second, _, _ -> t2_first
    | _ -> Lexing.compare_pos l1.Location.loc_end l2.Location.loc_end
    end
  (* Cursor inside one location: it has priority *)
  | 0, _ -> t1_first
  | _, 0 -> t2_first
  (* Cursor outside locations: favor before *)
  | n, m when n > 0 && m < 0 -> t1_first
  | n, m when m > 0 && n < 0 -> t2_first
  (* Cursor is after both, select the closest one *)
  | _, _ -> Lexing.compare_pos l2.Location.loc_end l1.Location.loc_end

let best_node ?disambiguate pos = function
  | [] -> []
  | init :: xs ->
    let f acc x =
      let node1 = leaf_node acc and node2 = leaf_node x in
      let tie_break =
        Option.bind
          ~f:(fun disambiguate -> disambiguate node1 node2)
          disambiguate
      in
      if compare_locations ?tie_break pos (node_loc node1) (node_loc node2) <= 0
      then acc
      else x
    in
    List.fold_left ~f ~init xs

let enclosing ?disambiguate pos roots =
  match best_node ?disambiguate pos roots with
  | [] -> []
  | root -> best_node ?disambiguate pos (select_leafs pos root)

let deepest_before ?disambiguate pos roots =
  match enclosing ?disambiguate pos roots with
  | [] -> []
  | root ->
    let rec aux path =
      let node0 = leaf_node path in
      let loc0 = node_merlin_loc node0 in
      let select_candidate node acc =
        let loc = node_merlin_loc node in
        if
          path == root
          || Location_aux.compare_pos pos loc = 0
          || Lexing.compare_pos loc.Location.loc_end loc0.Location.loc_end = 0
        then
          match acc with
          | Some (loc', node') ->
            let tie_break =
              Option.bind
                ~f:(fun disambiguate -> disambiguate node node')
                disambiguate
            in
            if compare_locations ?tie_break pos loc' loc <= 0 then acc
            else Some (loc, node)
          | None -> Some (loc, node)
        else acc
      in
      match fold_node select_candidate node0 None with
      | None -> path
      | Some (_, node) -> aux (node :: path)
    in
    aux root

let range_enclosing ~start ~stop roots =
  List.filter
    ~f:(fun node ->
      let loc = node_loc node in
      let nstart = loc.loc_start and nend = loc.loc_end in
      let a = Lexing.compare_pos start nstart
      and b = Lexing.compare_pos stop nend in
      a >= 0 && b <= 0)
    (enclosing start roots)
