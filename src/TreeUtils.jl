module TreeUtils

using Graphs
using MetaGraphsNext
using Combinatorics
using TreesIO

### Functions to export
export get_leaves, get_nodes, get_shared_leaves, get_tree_fadj_list, get_taxa_translation_table, bbfs_get_bipartitions, quartet_topology, print_bipartitions, unweighted_path_distance, prune_tree, identify_clade_members, find_lca, find_lca_largest_subset, find_root_node_with_outgroup, root_tree, annotate_clades!, make_newick_rooted, identify_stem_edge, get_internal_edges, find_long_branch_stacks, get_outermoste_edge, identify_clade_for_removal, get_all_nodes_in_clade, colour_node!, annotate_node!
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

### Function to retain the intersection of leaves from two trees (shared leaves) 
function get_shared_leaves(treeA:: MetaGraph, TreeB::MetaGraph)::Set{String}
	
    ## return value:
    shared::Set{String}= Set{String}()
    ##
	
    leavesA = get_leaves(treeA)
    leavesB = get_leaves(TreeB)
	
	
    shared= intersect(leavesA, leavesB)
    return shared
end

### This is a general helper: standardise the way we get the list of all nodes from a tree (get_nodes, get_leaves get_shared leaves) 
function get_nodes(tree::MetaGraph)::Set{String}
    return Set(labels(tree)) ## uses a MetaGraph function
end

### This is a UTILITY to get the forward adjacency list from MetaGraph. 
### Needed in the BFS version to get the clades in a tree
### This is a more efficient way to do BFS that starting from leaves
### In the future all BFS should use this approach and this helper.   
function get_tree_fadj_list(tree::MetaGraph)::Vector{Vector{Int64}}
	
    ### rerturned
    tree_adj_list::Vector{Vector{Int64}}=Vector{Vector{Int64}}()

    ### function itself
    ### uses function from Graph/MetaGraph package (graph.fadjlist)
    return tree.graph.fadjlist
end

### This UTILITY is also for BFS. To be used with get_tree_fadj_list() in fast BFS.
function get_taxa_translation_table(tree::MetaGraph)::Dict{Int64, String}
    
    ### rerturned
    translation_table::Dict{Int64, String}=Dict{Int64, String}()
    return tranlation_table= tree.vertex_labels
end

## This is a KEY function. Get all clades in a tree their stem BL and support.
## This underpins Component COnsensus methods: Strict, Maj Rule, RF-Dist etc.  
## takes a tree and gets its bipartitions, as well as supporting info bl of bipartition (edge between the two clades) and suport for that edge.
## The function works on a tree at a time its a generic Utility for TreesUtils
## bbfs stands for BLOCKED_BFS
function bbfs_get_bipartitions(tree::MetaGraph, graph_adj_list::Vector{Vector{Int64}}, translation_table::Dict{Int64,String})::Tuple{Vector{Tuple{Set{String},Set{String}}}, Dict{Tuple{Set{String},Set{String}},Float64}, Dict{Tuple{Set{String},Set{String}},Float64}, Int64}

    ## returned bipartitions is the key.  The other are accessory
    bipartitions::Vector{Tuple{Set{String},Set{String}}} = Vector{Tuple{Set{String},Set{String}}}()
        
    ntaxa::Int64= 0 ##### accessory returned value necessary for some downstream computations (e.g. normalisations)
        
    bips_supports::Dict{Tuple{Set{String},Set{String}},Float64} = Dict{Tuple{Set{String},Set{String}},Float64}()
        
    bips_bls::Dict{Tuple{Set{String},Set{String}},Float64} = Dict{Tuple{Set{String},Set{String}},Float64}()
    ###

    ### get the leaves Set.  This is to know nodes to skip
    leaves_set::Set{Int64} = Set{Int64}()
    for (index, neighbours) in enumerate(graph_adj_list)
        if length(neighbours) == 1
        push!(leaves_set, index)
        end
    end
    ntaxa= length(leaves_set)
            
    #### modified bfs with bloked nodes to get splits out
    #### This gets the bipartitions/splits
    for node::Int64 in 1:length(graph_adj_list)
        if length(graph_adj_list[node]) == 1 ## skip leaves as enry points
            continue
        end
        println("travrsing tree from node $(node)")
        for blocked_node in graph_adj_list[node]
            leaves_on_inner_side::Vector{Int64} = Vector{Int64}() ## these are nodes on the node side of the edge (inner) in opposition to outer side of edge (blocked node side)
            visited_nodes::Set{Int64}= Set{Int64}([blocked_node, node]) ### Key step add the blocked node to visited so it will never be seen
            queued_neighbours_of_node::Vector{Int64}= [neighbour for neighbour::Int64 in graph_adj_list[node]]
            while !isempty(queued_neighbours_of_node)
                (current_node)= popfirst!(queued_neighbours_of_node)
                if current_node in visited_nodes
                   continue
                end
                push!(visited_nodes, current_node)
                if length(graph_adj_list[current_node]) ==1
                   push!(leaves_on_inner_side, current_node)
                end
                for nb::Int64 in graph_adj_list[current_node]
                   if !(nb in visited_nodes)
                       push!(queued_neighbours_of_node, nb)
                   end
                end
            end
            inner_side_sorted = sort(leaves_on_inner_side)
            outer_side_sorted = sort([l for l in leaves_set if !(l in leaves_on_inner_side)])
            if length(inner_side_sorted) == 1
                continue
            end

            ## get node and blocked_node labels for EdgeData lookup
            ## this is to get support and bl to do
            ## weighted RF and other functions where we need extra info on the bipartition
            node_label::String = translation_table[node]
            blocked_label::String = translation_table[blocked_node]

            ## get support and branch length from EdgeData
            edge_support::Union{Float64,Missing} = missing
            edge_bl::Union{Float64,Missing} = missing

            ## edge_data is a TreesIO defined struct. it is a dict storing bl and support.  Accessible via a tuple of nodes.
            ## we do not know if a branch was initially stored  nl-bl or bl-nl so we test both possibilities.
            if !tree[node_label].is_a_leaf && !tree[blocked_label].is_a_leaf
                if haskey(tree.edge_data, (node_label, blocked_label))
                    edge = tree.edge_data[(node_label, blocked_label)]
                    edge_support = edge.support
                    edge_bl = edge.length
                elseif haskey(tree.edge_data, (blocked_label, node_label))
                    edge = tree.edge_data[(blocked_label, node_label)]
                    edge_support = edge.support
                    edge_bl = edge.length
                end
            end
                        
            if length(inner_side_sorted) < length(outer_side_sorted)
                inner_labeled = Set(sort([translation_table[i] for i in inner_side_sorted]))
                outer_labeled = Set(sort([translation_table[i] for i in outer_side_sorted]))
                bip = (inner_labeled, outer_labeled)
                push!(bipartitions, (inner_labeled, outer_labeled))

                ## add sup vals or bl when present or NaN when absent
                if ismissing(edge_support)
                    bips_supports[bip]= NaN
                else
                bips_supports[bip] = edge_support
                end
                if ismissing(edge_bl)
                    bips_bls[bip] = NaN
                else
                    bips_bls[bip] = edge_bl
                end
                ###
                
            elseif length(inner_side_sorted) == length(outer_side_sorted)
                if inner_side_sorted < outer_side_sorted
                    inner_labeled = Set(sort([translation_table[i] for i in inner_side_sorted]))
                    outer_labeled = Set(sort([translation_table[i] for i in outer_side_sorted]))
                    bip = (inner_labeled, outer_labeled)
                    push!(bipartitions, (inner_labeled, outer_labeled))
                        
                    ## add sup vals or bl when present or NaN when absent
                    if ismissing(edge_support)
                        bips_supports[bip]= NaN
                    else
                        bips_supports[bip] = edge_support
                    end
                    if ismissing(edge_bl)
                        bips_bls[bip] = NaN
                    else
                        bips_bls[bip] = edge_bl
                    end
                    ###   
                end
            end
        end
    end
    bipartitions = unique(bipartitions)
    return bipartitions, bips_supports, bips_bls, ntaxa
end
###

### quartet topology find the correct quartets associated with each node in a tree.
## underpins all consensus method based on quartets
function quartet_topology(tree::MetaGraph, A::String, B::String, C::String, D::String)::Union{String,Nothing}
    candidate_pairings = [
        (A, B, C, D, "AB|CD"),
        (A, C, B, D, "AC|BD"),
        (A, D, B, C, "AD|BC")
    ]
    
    for (x, y, w, z, label) in candidate_pairings
        lca_xy = find_lca(tree, [x, y],"quartet_pair"; warn_on_failure=false)
        if isnothing(lca_xy)
            continue
        end
        ## check whether one side of lca_xy (blocking some neighbour)
        ## gives exactly {x, y} — confirming x,y form a clade excluding w,z
        for blocked in neighbor_labels(tree, lca_xy)
            leaves::Set{String} = Set{String}()
            visited::Set{String} = Set{String}([blocked])
            queue::Vector{String} = [lca_xy]
            while !isempty(queue)
                current::String = popfirst!(queue)
                if current in visited
                    continue
                end
                push!(visited, current)
                if tree[current].is_a_leaf
                    push!(leaves, current)
                end
                for nb::String in neighbor_labels(tree, current)
                    if !(nb in visited)
                        push!(queue, nb)
                    end
                end
            end
            if leaves == Set([x, y])
                return label
            end
        end
    end
    return nothing  ## no pairing formed a clean 2-taxon clade — unresolved/polytomy
end
###

### This function print all the bipartitions (down to quartets) in a tree to scree. 
function print_bipartitions(trees::Vector{MetaGraph})
    for (i, tree) in enumerate(trees)
        fadj = get_tree_fadj_list(tree)
        tt = get_taxa_translation_table(tree)
        (bips, _, _, _) = bbfs_get_bipartitions(tree, fadj, tt)
        println("Tree $i:")
        for (inner, outer) in bips
            println("  $(join(sort(collect(inner)),",")) | $(join(sort(collect(outer)),","))")
        end
    end
    return nothing
end









### This function calculate the distance between two nodes 
### as the number of hops / edges / nodes between the start and target
### This is a standard BSF.
function unweighted_path_distance(tree::MetaGraph, starting_point::String, target_node::String)::Union{Int64,Nothing}
    visited::Set{String} = Set{String}()
    queue::Vector{String} = [starting_point]
    distance::Vector{Int64} = [0]
    while !isempty(queue)
        current= popfirst!(queue)
        current_distance=popfirst!(distance)
        if current == target_node
            return current_distance
        end
        if current in visited
            continue
        end
        push!(visited, current)
        for nb in neighbor_labels(tree, current)
            if !(nb in visited)
                push!(queue, nb) 
                push!(distance, current_distance + 1)
            end
        end
    end
    return nothing 
end

### Takes a tree and a set of leaves to keep, delete the other leaves and generate a new tree.  
### This is useful when we have a bunch of trees we want to remove taxa from (we pass the leaves to keep).
### Usually the list of leaves to keep is the intersection of the leaves in two or more trees 
function prune_tree(tree::MetaGraph, leaves_to_keep::Set{String})::MetaGraph

    ### The idea is that we do not want to modify the trees in place so we deepcopy
    pruned = deepcopy(tree)
    
    ## remove leaves not in keep set
    for node::String in collect(labels(pruned))
        if pruned[node].is_a_leaf && !(node in leaves_to_keep)
            rem_vertex!(pruned, code_for(pruned, node)) ### rem_vertex! is a MetaGraph function
        end
    end
    
    ## collapse degree-2 internal nodes
    changed::Bool = true
    while changed
        changed = false
        for node::String in collect(labels(pruned)) ## list of all nodes inernal & leaves
            if !pruned[node].is_a_leaf ### Check that node NOT a leaf
                nbs = collect(neighbor_labels(pruned, node))
                if length(nbs) == 2
                    ## if an internal has two neighbours only get BLs both ways
                    bl1::Union{Float64,Missing} = pruned[node, nbs[1]].length ## here syntax clear get length for edge defined by node and nbs1
                    bl2::Union{Float64,Missing} = pruned[node, nbs[2]].length # same for nbs 2
                    
                    ## sum branch lengths of two edges — handle missing
                    new_bl::Union{Float64,Missing} = missing
                    if ismissing(bl1) && ismissing(bl2)
                       new_bl = missing
                    elseif ismissing(bl1)
                      new_bl = bl2
                    elseif ismissing(bl2)
                       new_bl = bl1
                    else
                        new_bl = bl1 + bl2
                    end
                    
                    ## connect the two neighbours directly
                    pruned[nbs[1], nbs[2]] = EdgeData(new_bl)
                    
                    ## remove the degree-2 node
                    rem_vertex!(pruned, code_for(pruned, node))
                    changed = true
                    break 
                    ## Break exits the inner loop (here for loop)
                    ## Key. We changed leaves set in place (rem_vertex!)
                    ## So we must restart from scratch working on reduced set.
                    ## while stay true so this is repeated till all 2d node deleted
                end
            end
        end
    end
    return pruned
end
###

### find the lca of a set of taxa in the metagraphs (treated as unrooted) so check all possible clades using blocked BFS.
function find_lca(unrooted_tree::MetaGraph, taxa::Vector{String}, clade_name::String="unknown"; warn_on_failure::Bool=true)::Union{String,Nothing}

    taxa_set::Set{String} = Set{String}(taxa)
    
    for node_label::String in labels(unrooted_tree)
        if unrooted_tree[node_label].is_a_leaf
            continue  ## LCA must be an internal node (unless taxa_set has size 1, handled elsewhere)
        end
        for blocked::String in neighbor_labels(unrooted_tree, node_label)
            ## BFS from node_label, blocking this neighbour direction
            leaves::Set{String} = Set{String}()
            visited::Set{String} = Set{String}([blocked])
            queue::Vector{String} = [node_label]
            while !isempty(queue)
                current::String = popfirst!(queue)
                if current in visited
                    continue
                end
                push!(visited, current)
                if unrooted_tree[current].is_a_leaf
                    push!(leaves, current)
                end
                for nb::String in neighbor_labels(unrooted_tree, current)
                    if !(nb in visited)
                        push!(queue, nb)
                    end
                end
            end
            if leaves == taxa_set
                return node_label
            end
        end
    end
    
    ## The error message is in an if because it is true that lca not found (and correct) when used to identify quartets: quartet_topology() function 
    if warn_on_failure
    @warn "Could not find a LCA for clade $(clade_name) that included ALL taxa in its definition — the full set of taxa in $(clade_name) is not monophyletic in tree"
    end
    ##

    return nothing
end 
####

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
#### priority 3 — original root edge from newick stored in graph_data
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
            if haskey(unrooted_tree.graph_data, "original_root_edge")
                (node_a, node_b) = unrooted_tree.graph_data["original_root_edge"]
                root_name = node_a
            end
        end
    ## priority 3 — original root edge from newick stored in graph_data
    elseif haskey(unrooted_tree.graph_data, "original_root_edge")
        (node_a, node_b) = unrooted_tree.graph_data["original_root_edge"]
        root_name = node_a
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
