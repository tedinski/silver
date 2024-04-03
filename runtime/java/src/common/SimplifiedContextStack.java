package common;

import java.util.Iterator;
import java.util.Stack;
import java.util.Arrays;
import java.util.ArrayList;
import java.util.List;

// Basically a decorator over a ContextStack to 
// generate a simplified (one node per tree order) stack
public class SimplifiedContextStack {

    public SimplifiedContextStack(ContextStack full_stack) {
        this.full_stack = full_stack;
        this.partition = new int[full_stack.get_height()];
    }

    public Stack<SimplifiedContextBox> getSimplifiedStack() {
        this.need_set_all_prods = true;
        this.makeSimplifiedStack();
        
        // UNCOMMENT-ME. FOR-DEMO
        System.out.println("NEW SIMPLIFIED STACK SIZE: " + this.simple_stack.size());
        return this.simple_stack;
    }

    private void makeSimplifiedStack() {
        
        // Clear previous simplified stack to get a brand new one
        this.simple_stack = new Stack<SimplifiedContextBox>();
        
        this.fillInPartition();
        
        // Now make one box per partition
        int prev_partition_index = 0; 
        int start = 0;
        int end = -1;

        // System.out.println(this.partition[0]);
        for (int i = 0; i < this.partition.length; i++) {
            
            if (this.partition[i] > prev_partition_index) {
                // Make box on existing start and end
                SimplifiedContextBox sbox = this.makeSimplifiedBox(start, end);
                this.simple_stack.push(sbox);
                start = i;
                end = start;
                prev_partition_index++;
            }
            else {
                end++;
            }
        }
        // Last one
        SimplifiedContextBox sbox = this.makeSimplifiedBox(start, end);
        this.simple_stack.push(sbox);
    }

    // Inclusive Partition Indices
    private SimplifiedContextBox makeSimplifiedBox(int i, int j) {
        
        // UNCOMMENT-ME. FOR-DEMO
        // !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
        // System.out.println("MAKING SIMPLIFIED BOX: " + i + ", " + j);

        if (i > j) {
            System.out.println("Invalid Partition Indices: " + i + ", " + j);
            return null;
        }
        
        // 4 sections to fill in 
        SimplifiedContextBox sbox = new SimplifiedContextBox();

        NodeContextMessage first = this.full_stack.get(i);
        NodeContextMessage last = this.full_stack.get(j);
        // System.out.println(first.getProdName());
        
        // 1. Tree Order Trivial
        sbox.translation_x = first.getTranslationX();
        sbox.higher_order_y = first.getHigherOrderY();

        // // 2. Text Syntax (highlight later when rendering)
        sbox.text_syntax = first.getTextRepr();
        sbox.syntax_to_highlight = last.getTextRepr();

        // // 3. Need some counting logic to keep track of unique indices
        this.SetAllProds();
        sbox.prods_visited = Arrays.copyOfRange(this.productions, i, j + 1);

        // // Make features list now (list, not array, since unknown length)
        sbox.features = new ArrayList<Feature>();
        this.fillInFeaturesList(sbox, i, j);
        
        // for (i = 0; i < sbox.prods_visited.length; i++) {
        //     System.out.println(sbox.prods_visited[i]);
        // }
        // System.out.println("text: " + sbox.text_syntax);
        // System.out.println("to highlight: " + sbox.syntax_to_highlight);

        
        // UNCOMMENT-ME. FOR-DEMO
        // !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
        // System.out.println("first prod: " + sbox.prods_visited[0]);
        // if (sbox.features.size() > 0) {
        //     System.out.println("first feature: " + sbox.features.get(0));
        // }
        
        return sbox;
    }

    private void fillInFeaturesList(SimplifiedContextBox sbox, int i, int j) {
        
        for (int k = i; k <= j; k++) {
            NodeContextMessage node = this.full_stack.get(k);

            if (node.isRedex()) {
                String nodeName = productions[k].toString();
                String targetName = "";
                if (k < j) {
                    targetName = productions[k + 1].toString();
                }
                Feature f = new Feature(nodeName, "redex", targetName);
                sbox.features.add(f);
            }
            if (node.isContractum()) {
                String nodeName = productions[k].toString();
                String targetName = "";
                if (k > 0) {
                    targetName = productions[k - 1].toString();
                }
                Feature f = new Feature(nodeName, "contractum", targetName);
                sbox.features.add(f);
            }
            if (node.isNew()) {
                String nodeName = productions[k].toString();
                // No origin tracking to find prod name of origin
                Feature f = new Feature(nodeName, "new");
                sbox.features.add(f);
            }
            if (node.isAttributeRoot()) {
                String nodeName = productions[k].toString();
                String targetName = "";
                if (k > 0) {
                    targetName = productions[k - 1].toString();
                }
                Feature f = new Feature(nodeName, "attribute root", targetName);
                sbox.features.add(f);
            }
        }
    }

    private void SetAllProds() {
        
        // System.out.println(this.need_set_all_prods);
        if (! this.need_set_all_prods) {
            return;
        }
        // Only do this once 
        // Not worried about multiple instances of SimplifiedContextStack;
        // rather, don't want to do this for every SimplifiedContextBox created

        ProductionName all_prods[] = new ProductionName[this.full_stack.get_height()];
        for (int index = 0; index < this.full_stack.get_height(); index++) {
            // System.out.println(all_prods.length);
            ProductionName pn = new ProductionName(this.full_stack.get(index).getProdName(), -1);
            all_prods[index] = pn;
        }


        // Going to be fine with O(n^2) worst case time complexity here for now
        // Simply a prototype implementation of simplified stack

        // Unique prod names get the 0 index (not to be displayed)
        // Non-unique prod names are numbered from 1..n, so need extra
        // scan afterwards to separate unique 1 -> 0 from actual 1 
        for (int prod_index = 0; prod_index < all_prods.length; prod_index++) {
            
            int seq_num = 1;
            String name = all_prods[prod_index].name;
            
            for (int visit_index = 0; visit_index < prod_index; visit_index++) {
                String cur_name = all_prods[visit_index].name;
                if (cur_name.compareTo(name) == 0) {
                    seq_num++;
                }
            }
            all_prods[prod_index].index = seq_num;
        }

        // All prod indices >= 1. Find if need to differentiate 1 into 0 now
        // if truly unique and not start of 1..n sequence of indices
        for (int prod_index = 0; prod_index < all_prods.length; prod_index++) {
            
            if (all_prods[prod_index].index == 1) {
                boolean is_unique = true;
                for (int k = 0; k < all_prods.length; k++) {
                    if (k != prod_index && 
                        (all_prods[k].name.compareTo(all_prods[prod_index].name) == 0)) {
                            is_unique = false;
                            break;
                        }
                }
                if (is_unique) {
                    all_prods[prod_index].index = 0;
                }
            }
        }

        this.productions = all_prods;
        this.need_set_all_prods = false;
        // System.out.println(this.productions[0]);
        // String res = "Prods visted: [\n";
        // for (int i = 0; i < this.productions.length; i++) {
        //     res += "\t" + this.productions[i].name + ", \n";
        // }
        // res += "]";
        // System.out.println(res);

        return;
    }

    private void fillInPartition() {

        this.partition = new int[full_stack.get_height()];

        int previous_x = 0;
        int previous_y = 0;
        int partition_index = 0;
        for (int i = 0; i < this.full_stack.get_height(); i++) {
            NodeContextMessage node = this.full_stack.get(i);
            int cur_x = node.getTranslationX();
            int cur_y = node.getHigherOrderY();
            if (cur_x == previous_x && cur_y == previous_y) {
                // Within same set of partition
                this.partition[i] = partition_index;
            }
            else {
                previous_x = cur_x;
                previous_y = cur_y;
                // Increment partition index
                partition_index++;
                this.partition[i] = partition_index;
            }
        }

        // String res = "PARTITION: [\n";
        // for (int i = 0; i < this.partition.length; i++) {
        //     res += "\t" + this.partition[i] + ", \n";
        // }
        // res += "]";
        // System.out.println(res);
    }

    // public static class Production {
    //     public String name;
    //     public int  index;

    //     public Production(String name, int index) {
    //         this.name = name;
    //         this.index = index;
    //     }

    //     public String toString() {
    //         if (this.index == 0) {
    //             return this.name;
    //         }
    //         else {
    //             return this.name + " (" + this.index + ")";
    //         }
    //     }
    // }

    private ContextStack full_stack;
    private Stack<SimplifiedContextBox> simple_stack = 
        new Stack<SimplifiedContextBox>();
    
    private boolean need_set_all_prods = true;
    private ProductionName productions[];

    // // Put 0 for each respective element in the first 
    // // stack partition, then 1, etc. Index 0 into stack is bottom
    private int[] partition;
    
}




