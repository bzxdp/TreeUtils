module TreeUtils

using Graphs
using MetaGraphsNext
using TreesIO

### Functions to export
export get_leaves, identify_clade_members, find_lca, find_lca_largest_subset, find_root_node_with_outgroup, root_tree, annotate_clades!, make_newick_rooted, identify_stem_edge, get_internal_edges, find_long_branch_stacks, get_outermoste_edge, identify_clade_for_removal, get_all_nodes_in_clade, colour_node!, annotate_node!
###

### function to add colours to a Metagraph
function colour_node!(tree::MetaGraph, node_to_colour::String, colour::String)
        tree[node_to_colour].graphical_attribute= colour
end

### function to add node annotations (e.g. cladename) to metagraph
function annotate_node!(tree::MetaGraph, node_to_annotate::String, annotation::String)
	tree[node_to_annotate].other_attribute= annotation
end

#### function to get the list of leaves in a metagraph tree
function get_leaves(unrooted_tree::MetaGraph)::Set{String}
    taxa_in_tree::Set{String}=Set{String}()
    for node_label::String in labels(unrooted_tree) # labels is a function in Graph/Metagraph
        if unrooted_tree[node_label].is_a_leaf # gets the value from structure described at top
            push!(taxa_in_tree, node_label) #this defines the full set of leaves in a tree as a set
        end
    end
    return taxa_in_tree
end
############

#### find the last common ancestor of a set of taxa in a metagraph tree
function find_lca(unrooted_tree::MetaGraph, taxa::Vector{String}, clade_name::String="unknown")::Union{String,Nothing}
    
    ## do a post order traversal to root and find the node that is ancestor of all taxa
    ## for each node collect the set of leaves in its subtree
    ## the LCA is the deepest node whose subtree contains all taxa
    ## Needs a root node to provide directionality to search (this is not a biological root) any random internal node will do.
    if haskey(unrooted_tree.graph_data, "original_root") ## if a rooting point is stored, use it -- This is from Newick_to_Metagraph function in TreeIO
        root::String = unrooted_tree.graph_data["original_root"]
    else
        all_leaves::Vector{String} = sort(collect(get_leaves(unrooted_tree))) ## else root alphabetically arbitrary but repeatible -- will root tree on taxon with lower alphabet letter
        root = all_leaves[1]
    end
    taxa_set::Set{String} = Set{String}(taxa)

    ## recursive helper that returns the set of leaves in the subtree rooted at node
    ## and records the LCA when found
    lca_found::Ref{Union{String,Nothing}} = Ref{Union{String,Nothing}}(nothing)

    function get_leaves_in_subtree(node_name::String, parent_name::Union{String,Nothing})::Set{String}
        leaves::Set{String}= Set{String}()

        #base case
        if unrooted_tree[node_name].is_a_leaf
            push!(leaves, node_name)
            return leaves
        end

        for neighbour::String in neighbor_labels(unrooted_tree, node_name) ## loop neighbor one by one.
            if neighbour == parent_name
                continue
            end
            child_leaves::Set{String} = get_leaves_in_subtree(neighbour, node_name)
            leaves= union!(leaves, child_leaves)
        end

        ## check if this node is the LCA — its subtree contains all taxa
        ## and we have not found the LCA yet

        if isnothing(lca_found[]) && issubset(taxa_set, leaves) && leaves == taxa_set
            lca_found[] = node_name
        end
        return leaves
    end
    get_leaves_in_subtree(root, nothing) ### start recursion by passing the root node.  This is whatever was root when reading newick.  Does not ned to be real root. just a reference for traversal

    if isnothing(lca_found[])
        @warn "Could not find a LCA for clade $(clade_name) that included ALL taxa in its definition — the full set of taxa in $(clade_name) is not monophyletic in tree"
    end
    return lca_found[]
end

#### find the LCA of the largest monophyletic subset of taxa
#### handles missing taxa and non-monophyletic clades

function find_lca_largest_subset(unrooted_tree::MetaGraph, taxa::Vector{String}, clade_name::String="unknown")::Tuple{Union{String,Nothing}, Vector{String}}
    result = identify_clade_members(unrooted_tree, taxa)
    if isnothing(result)
        @warn "No taxa from clade $(clade_name) found in tree"
        return nothing, Vector{String}()
    end
    (taxa_in_tree, missing_taxa) = result

    if !isempty(missing_taxa)
        @warn "Some taxa not in tree $(join(missing_taxa, ", ")) — using intersection"
    end

    if length(taxa_in_tree) < 2
        @warn "Only one taxon from clade $(clade_name) present in tree — cannot define a monophyletic clade"
        return nothing, Vector{String}()
    end

    present_taxa::Set{String} = Set{String}(taxa_in_tree)
    best_fragment::Set{String} = Set{String}()

    ## for each directed edge (node_label → neighbour) collect all leaves on the neighbour side
    ## if all those leaves are clade taxa and there are more than current best — keep it
    for node_label::String in labels(unrooted_tree)
        for neighbour::String in neighbor_labels(unrooted_tree, node_label)

            taxa_on_this_side::Set{String} = Set{String}()
            visited::Set{String} = Set{String}([node_label])
            queue::Vector{String} = [neighbour]
            while !isempty(queue)
                current::String = popfirst!(queue)
                if current in visited
                    continue
                end
                push!(visited, current)
                if unrooted_tree[current].is_a_leaf
                    push!(taxa_on_this_side, current)
                end
                for nb::String in neighbor_labels(unrooted_tree, current)
                    if !(nb in visited)
                        push!(queue, nb)
                    end
                end
            end

            ## key check: all leaves on this side must be clade taxa (issubset)
            ## and there must be at least 2 and more than current best
            if length(taxa_on_this_side) >= 2 &&
               issubset(taxa_on_this_side, present_taxa) &&
               length(taxa_on_this_side) > length(best_fragment)
                best_fragment = taxa_on_this_side
            end
        end
    end
    
    if length(best_fragment) < 2
        @warn "No monophyletic subset of size >= 2 found for $(clade_name) — all taxa scattered"
        return nothing, Vector{String}()
    end
    
    ## instead of calling find_lca, find the boundary node directly
    ## best_fragment was found on the neighbour side of some edge
    ## re-scan to find which edge gave best_fragment and return the neighbour node
    best_fragment_set::Set{String} = best_fragment
    best_lca_node::Union{String,Nothing} = nothing
    
    for node_label::String in labels(unrooted_tree)
    for neighbour::String in neighbor_labels(unrooted_tree, node_label)
        taxa_on_this_side::Set{String} = Set{String}()
        visited::Set{String} = Set{String}([node_label])
        queue::Vector{String} = [neighbour]
        while !isempty(queue)
            current::String = popfirst!(queue)
            if current in visited; continue; end
            push!(visited, current)
            if unrooted_tree[current].is_a_leaf
                push!(taxa_on_this_side, current)
            end
            for nb::String in neighbor_labels(unrooted_tree, current)
                if !(nb in visited); push!(queue, nb); end
            end
        end
        if taxa_on_this_side == best_fragment_set
            best_lca_node = neighbour
            break
        end
    end
    if !isnothing(best_lca_node); break; end
end
    
    best_fragment_vec::Vector{String} = collect(best_fragment)
    @warn "Clade $(clade_name) not monophyletic — returning largest monophyletic subset of $(length(best_fragment)) of $(length(taxa_in_tree)) taxa"
    return best_lca_node, best_fragment_vec
    
end

########

#### function identifying what taxa in a clade passed list are in a tree does not check monophyly
function identify_clade_members(unrooted_tree::MetaGraph,clade::Vector{String})::Union{Tuple{Vector{String},Vector{String}},Nothing} ### return tuple member of clade and missing taxa and warns that clade not present
    ## first get the taxa in the tree in a set
    taxa_in_tree= get_leaves(unrooted_tree)
    clade_as_a_set= Set(clade)

    #### find intersection of taxa in tree with taxa in clade
    relevant_taxa_in_tree::Vector{String}= collect(intersect(clade_as_a_set,taxa_in_tree))
    missing_taxa::Vector{String} = collect(setdiff(clade_as_a_set,taxa_in_tree))

    if isempty(relevant_taxa_in_tree)
        @warn "no member of clade found in tree"
        return nothing
    end

    if !isempty(missing_taxa)
        @warn "Some taxa not in tree $(join(missing_taxa, " "))"
    end
    return relevant_taxa_in_tree, missing_taxa
end
#########

#### find root node for outgroup rooting — thin wrapper around find_lca_largest_subset
#### returns the NEIGHBOUR of the outgroup LCA — i.e. the ingroup side node
function find_root_node_with_outgroup(unrooted_tree::MetaGraph, outgroups::Vector{String})::Union{String,Nothing}

    ## find LCA of outgroup taxa — this is the ancestor of the outgroup clade
    (lca, _) = find_lca_largest_subset(unrooted_tree, outgroups)
    if isnothing(lca)
        return nothing
    end

    ## the rooting node is the neighbour of the LCA that is NOT an outgroup taxon
    ## i.e. the node on the ingroup side of the outgroup split
    outgroups_set::Set{String} = Set{String}(outgroups)
    for neighbour::String in neighbor_labels(unrooted_tree, lca)
        if !(neighbour in outgroups_set)
            return neighbour
        end
    end

    return nothing
end
#################

#### find root of tree using outgroup — calls find_root_node_with_outgroup
function root_tree(unrooted_tree::MetaGraph,outgroups::Vector{String})::Union{String,Nothing}
    result = identify_clade_members(unrooted_tree, outgroups) # use helper to get the outgroups & missing taxa
    if isnothing(result) ### Handle first the case in which the tuple is empty then split it into two variables.
        @warn "all outgroup taxa are missing from the tree. The tree will use the original rooting as in the newick file that has been read."
        return nothing
    end

    (outgroups_in_tree, missing_outgroups) = result

    if !isempty(missing_outgroups)
        @warn "Some outgroups not in tree $(join(missing_outgroups, ", ")) — rooting on intersection"
    end

    ## find root node using outgroup — calls find_lca_largest_subset internally
    root_point = find_root_node_with_outgroup(unrooted_tree, outgroups_in_tree)
    return root_point
end

#### annotate internal nodes with clade names from a clade definition file
#### format: CladeName taxon1 taxon2 taxon3 ...
#### stores mapping clade_name → internal node ID in graph_data["clade_nodes"]
function annotate_clades!(unrooted_tree::MetaGraph, clade_file::String)::Nothing

    if !haskey(unrooted_tree.graph_data, "clade_nodes")
        unrooted_tree.graph_data["clade_nodes"] = Dict{String,String}()
    end

    clade_nodes::Dict{String,String} = unrooted_tree.graph_data["clade_nodes"]

    open(clade_file, "r") do fh
        for line::String in eachline(fh)
            line = String(strip(line))
            if isempty(line)
                continue
            end
            fields::Vector{String} = split(line)
            if length(fields) < 2
                @warn "Skipping malformed clade line: $line"
                continue
            end
            clade_name::String = fields[1]
            clade_taxa::Vector{String} = fields[2:end]

            (lca_node, _) = find_lca_largest_subset(unrooted_tree, clade_taxa)

            if isnothing(lca_node)
                @warn "Could not find LCA node for clade $clade_name — skipping"
                continue
            end

            clade_nodes[clade_name] = lca_node
            @info "Clade $clade_name assigned to node $lca_node"
        end
    end

    return nothing
end

#### This turns a metagraph into a rooted newick string using the rooting priority logic
#### priority 1 — explicit root passed as argument
#### priority 2 — outgroup stored in graph_data
#### priority 3 — original root from newick stored in graph_data
#### priority 4 — alphabetical fallback via make_newick_unrooted
function make_newick_rooted(unrooted_tree::MetaGraph, root_name::Union{String,Nothing}=nothing)::String

    ## priority 1 — explicit root passed as argument
    if !isnothing(root_name)
        ## use as is
    ## priority 2 — outgroup stored in graph_data
    elseif haskey(unrooted_tree.graph_data, "outgroup")
        outgroup::Vector{String} = unrooted_tree.graph_data["outgroup"]
        root_name = root_tree(unrooted_tree, outgroup)
        if isnothing(root_name)
            ## root_tree already warned — fall to priority 3
            if haskey(unrooted_tree.graph_data, "original_root")
                root_name = unrooted_tree.graph_data["original_root"]
            end
        end
    ## priority 3 — original root from newick stored in graph_data
    elseif haskey(unrooted_tree.graph_data, "original_root")
        root_name = unrooted_tree.graph_data["original_root"]
    end

    ## priority 4 — alphabetical fallback via make_newick_unrooted
    if isnothing(root_name)
        @warn "No root information available — writing unrooted newick with trifurcating base"
        return make_newick_unrooted(unrooted_tree)
    end

    ## recursive function to build newick string from a given root
    function build_newick(node_name::String, parent_name::Union{String,Nothing})::String

        ## get edge data to parent if not root
        bl::Union{Float64,Missing} = missing
        support::Union{Float64,Missing} = missing
        if !isnothing(parent_name)
            edge::EdgeData= unrooted_tree[parent_name, node_name]
            bl = edge.length
            support = edge.support
        end

        ## format branch length and support strings
        bl_str::String = ismissing(bl) ? "" : ":$(bl)"
        support_str::String = ismissing(support) ? "" : "$(support)"

        ## base case — leaf node
        if unrooted_tree[node_name].is_a_leaf
            return "$(node_name)$(bl_str)"
        end

        ## recursive case — internal node
        children_strings::Vector{String} = Vector{String}()
        for neighbour::String in neighbor_labels(unrooted_tree, node_name)
            if neighbour == parent_name ### skip parent to avoid infinite loop — key for unrooted traversal
                continue
            end
            child_string::String = build_newick(neighbour, node_name)
            push!(children_strings, child_string)
        end

        children_joined::String = join(children_strings, ",")

        if isnothing(parent_name)
            ## root node — no branch length or support above it
            return "($(children_joined))"
        else
            return "($(children_joined))$(support_str)$(bl_str)"
        end

    end

    newick_string::String = build_newick(root_name, nothing) * ";"
    return newick_string
end

#### identify the stem edge subtending a clade
#### given the LCA node and the clade taxa finds the neighbour on the stem side
#### i.e. the neighbour whose subtree does NOT contain clade taxa
#### returns a tuple of the two node names defining the stem edge: (lca_node, stem_neighbour)
function identify_stem_edge(unrooted_tree::MetaGraph, lca_node::String, clade_taxa::Vector{String})::Union{Tuple{String,String},Nothing}

    clade_taxa_set::Set{String} = Set{String}(clade_taxa)

    ## for each neighbour of the LCA node check which side it is on
    ## the stem neighbour is the one whose subtree does NOT contain clade taxa
    for neighbour::String in neighbor_labels(unrooted_tree, lca_node)

        ## collect all leaves on the neighbour side using BFS
        taxa_on_this_side::Set{String} = Set{String}()
        visited::Set{String} = Set{String}([lca_node])
        queue::Vector{String} = [neighbour]
        while !isempty(queue)
            current::String = popfirst!(queue)
            if current in visited
                continue
            end
            push!(visited, current)
            if unrooted_tree[current].is_a_leaf
                push!(taxa_on_this_side, current)
            end
            for nb::String in neighbor_labels(unrooted_tree, current)
                if !(nb in visited)
                    push!(queue, nb)
                end
            end
        end

        ## if no clade taxa on this side — this is the stem neighbour
        if isempty(intersect(taxa_on_this_side, clade_taxa_set))
            return (lca_node, neighbour)
        end
    end

    ## should never reach here
    @warn "Could not find stem edge for lca node $lca_node"
    return nothing
end
######

#### extract internal branches as tuples of (node1, node2) — both nodes are internal
#### returns a Vector of tuples representing edges between two internal nodes
#### excludes terminal branches (leaf to internal node edges)
function get_internal_edges(unrooted_tree::MetaGraph)::Vector{Tuple{String,String}}

    internal_edges::Vector{Tuple{String,String}} = Vector{Tuple{String,String}}()
    seen_edges::Set{Tuple{String,String}} = Set{Tuple{String,String}}()

    for node_label::String in labels(unrooted_tree)
        if unrooted_tree[node_label].is_a_leaf
            continue
        end
        for neighbour::String in neighbor_labels(unrooted_tree, node_label)
            if unrooted_tree[neighbour].is_a_leaf
                continue
            end

            ## avoid counting each edge twice — undirected graph means
            ## (a,b) and (b,a) are the same edge but visited from both ends
            edge_key::Tuple{String,String} = node_label < neighbour ? (node_label, neighbour) : (neighbour, node_label)
            if edge_key in seen_edges
                continue
            end
            push!(seen_edges, edge_key)
            push!(internal_edges, edge_key)
        end
    end

    return internal_edges
end

function find_long_branch_stacks(unrooted_tree::MetaGraph, bls::Dict{Tuple{String,String},Float64},trigger::Float64,min_stack_length::Int64)::Vector{Vector{Tuple{String,String}}}

    canonical(u, v) = u < v ? (u, v) : (v, u)

    ## find all long internal edges
    canonical_long::Set{Tuple{String,String}} = Set{Tuple{String,String}}()
    for (edge, bl) in bls
        (u, v) = edge
        if !unrooted_tree[u].is_a_leaf && !unrooted_tree[v].is_a_leaf && bl > trigger
            push!(canonical_long, canonical(u, v))
        end
    end

    ## find connected components of long internal edges
    ## two long internal edges are stacked if they share an internal node
    visited_edges::Set{Tuple{String,String}} = Set{Tuple{String,String}}()
    stacks::Vector{Vector{Tuple{String,String}}} = Vector{Vector{Tuple{String,String}}}()

    for edge in canonical_long
        if edge in visited_edges
            continue
        end
        stack::Vector{Tuple{String,String}} = Vector{Tuple{String,String}}()
        queue::Vector{Tuple{String,String}} = [edge]
        while !isempty(queue)
            current_edge = popfirst!(queue)
            if current_edge in visited_edges
                continue
            end
            push!(visited_edges, current_edge)
            push!(stack, current_edge)
            (u, v) = current_edge
            for node in [u, v]
                for nb in neighbor_labels(unrooted_tree, node)
                    if !unrooted_tree[nb].is_a_leaf
                        candidate = canonical(node, nb)
                        if candidate in canonical_long && !(candidate in visited_edges)
                            push!(queue, candidate)
                        end
                    end
                end
            end
        end
        if length(stack) >= min_stack_length
            push!(stacks, stack)
        end
    end

    return stacks
end


function get_outermost_edge(unrooted_tree::MetaGraph,stack::Vector{Tuple{String,String}})::Tuple{String,String}
    best_edge = stack[1]
    best_larger_side = 0
    n_leaves = length(get_leaves(unrooted_tree))

    for (u, v) in stack
        leaves_v::Set{String} = Set{String}()
        visited::Set{String} = Set{String}([u])
        queue::Vector{String} = [v]
        while !isempty(queue)
            current = popfirst!(queue)
            if current in visited; continue; end
            push!(visited, current)
            if unrooted_tree[current].is_a_leaf
                push!(leaves_v, current)
            end
            for nb in neighbor_labels(unrooted_tree, current)
                if !(nb in visited); push!(queue, nb); end
            end
        end
        larger_side = max(length(leaves_v), n_leaves - length(leaves_v))
        if larger_side > best_larger_side
            best_larger_side = larger_side
            best_edge = (u, v)
        end
    end
    return best_edge
end


function identify_clade_for_removal(unrooted_tree::MetaGraph,long_branch_edge::Tuple{String,String})::Vector{String}

    (u, v) = long_branch_edge

    ## BFS from v excluding u
    leaves_v::Set{String} = Set{String}()
    total_bl_v::Float64 = 0.0
    visited_v::Set{String} = Set{String}([u])
    queue_v::Vector{String} = [v]
    while !isempty(queue_v)
        current = popfirst!(queue_v)
        if current in visited_v; continue; end
        push!(visited_v, current)
        if unrooted_tree[current].is_a_leaf
            push!(leaves_v, current)
        end
        for nb in neighbor_labels(unrooted_tree, current)
            if !(nb in visited_v)
                edge_data = unrooted_tree[current, nb]
                if !ismissing(edge_data.length)
                    total_bl_v += edge_data.length
                end
                push!(queue_v, nb)
            end
        end
    end

    ## BFS from u excluding v
    leaves_u::Set{String} = Set{String}()
    total_bl_u::Float64 = 0.0
    visited_u::Set{String} = Set{String}([v])
    queue_u::Vector{String} = [u]
    while !isempty(queue_u)
        current = popfirst!(queue_u)
        if current in visited_u; continue; end
        push!(visited_u, current)
        if unrooted_tree[current].is_a_leaf
            push!(leaves_u, current)
        end
        for nb in neighbor_labels(unrooted_tree, current)
            if !(nb in visited_u)
                edge_data = unrooted_tree[current, nb]
                if !ismissing(edge_data.length)
                    total_bl_u += edge_data.length
                end
                push!(queue_u, nb)
            end
        end
    end

    ## smaller side goes — tiebreak on higher total BL
    if length(leaves_v) < length(leaves_u)
        return collect(leaves_v)
    elseif length(leaves_u) < length(leaves_v)
        return collect(leaves_u)
    else
        return total_bl_v >= total_bl_u ? collect(leaves_v) : collect(leaves_u)
    end
end

function get_all_nodes_in_clade(tree::MetaGraph, lca_node::String, stem_neighbour::String)::Set{String}
    ## BFS from lca_node into the clade, blocked by stem_neighbour direction
    ## Returns all nodes (leaves and internal) on the clade side
    nodes::Set{String} = Set{String}()
    visited::Set{String} = Set{String}([stem_neighbour])  ## block this direction from the start
    queue::Vector{String} = [lca_node]
    while !isempty(queue)
        current::String = popfirst!(queue)
        if current in visited
            continue
        end
        push!(visited, current)
        push!(nodes, current)
        for nb::String in neighbor_labels(tree, current)
            if !(nb in visited)
                push!(queue, nb)
            end
        end
    end
    return nodes
end



end ### end of module TreeUtils
