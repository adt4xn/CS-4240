(**  CS 4240 FINAL PROJECT    **)

(** Here we implement a very simple database data structure and a few SQL-like
commands to go with it. The database is simply a list of columns (which
we define). A column is a function from "header" to some list (either a list
of nats or a list of strings. For simplicity sake, we assume there are only
two possible data types for the entries of this database, nat and string). 
Thus, again, a column is just a list of all the entries in said column. 
The commands we implement are 
   1. insert - insert a row of data into the table
   2. select - select a row of data to be passed to some other function
   3. drop_row - drop a row from the table
   4. drop_column - drop a column from the table   
   5. merge - merges two tables    **)

Require Export List.
Require Export String.
Open Scope string_scope.
Open Scope list_scope.
Require Import Ascii.
Require Import Arith.

(** This is the header data type. Headers are represented as nats  **)

Record col_header: Set := make_header {
  get_header_str: string
}. 

(**  column data type. it is a function from [nat] to [list nat] in which the
    nat is essentially the "header" of the column and the list is all the
    entries in that column  **)
Inductive column :=  
  | make_col_nat : col_header -> list nat -> column
  | make_col_string : col_header -> list string -> column.

(** table data type. it is just a list of columns  **)
Definition table := list column.


Example header1 := make_header "id numbers".
Example header2 := make_header "names".
Example column1 := make_col_nat header1 (1::2::3::nil).
Example column2 := make_col_string header2 ("John"::"Millie"::"Herbert"::nil).
Example table1 := column1::column2::nil.

(**  database data type. Is essentially just a list of rows  **)
Definition db := list table.

(** Insert into a column. If the column is a string type, the function
will attempt to insert the string parameter. If column is nat, then the nat **)
Definition colinsert (dbcol : column) (X: nat) (Y: string) : column :=
 match dbcol with
 | make_col_nat header listnat => make_col_nat header (X::listnat)
 | make_col_string header liststring => make_col_string header (Y::liststring)
 end.

Example minicolumn1 := make_col_nat header1 (4::nil).
Example minicolumn2 := make_col_string header2 ("Roxanne"::nil).
Example minitable1 := minicolumn1::minicolumn2::nil.

(** Insert a table of size one (such as minitable1, above) into a preexisting table **)
Fixpoint insert (dbtable sizeonetable : table) : table := 
 match dbtable with
 | nil => dbtable
 | cons h t =>
  match h with
  | make_col_nat mainheader mainlistnat =>
   match sizeonetable with
   | nil => dbtable
   | cons oh ot => 
    match oh with
    | make_col_nat oheader olistnat =>
     match olistnat with
     | _ :: _ :: _ => dbtable
     | nil => dbtable
     | cons val nil => (colinsert h val "null")::(insert t ot)
     end
    | make_col_string oheader oliststring => dbtable
    end
   end
  | make_col_string mainheader mainliststring =>
   match sizeonetable with
   | nil => dbtable
   | cons oh ot => 
    match oh with
    | make_col_string oheader oliststring =>
     match oliststring with
     | _ :: _ :: _ => dbtable
     | nil => dbtable
     | cons val nil => (colinsert h 0 val)::(insert t ot)
     end
    | make_col_nat oheader olistnat => dbtable
    end
   end
  end
 end.

Compute insert table1 minitable1.

(** A string equivalency function, necessary for checking names of fields against parameters, found from stack overflow **)
Fixpoint beq_str (sa sb : string) {struct sb}: bool := 
   match sa, sb with
 | EmptyString, EmptyString  => true
 | EmptyString, String b sb' => false
 | String a sa', EmptyString => false
 | String a sa', String b sb'=> match (ascii_dec a b) with 
                                | left _ => beq_str sa' sb'
                                | right _ => false
                                end
 end.

(** Takes in a table and a field name, and drops the column of the given name **)
Fixpoint dropcolumn(dbtable: table)(s: string) : table :=
  match dbtable with
  | nil => nil
  | cons h t => match h with
            | make_col_string head list =>
              if (beq_str (get_header_str head) s) then t else h::(dropcolumn t s)
            | make_col_nat hnat lnat =>
              if (beq_str (get_header_str hnat) s) then t else h::(dropcolumn t s)
end
end.

Check (get_header_str header1).
Compute (get_header_str header1).
Compute dropcolumn table1 "names".

(** A helper function for selectWhere. Finds the index of the given value among a list of nats **)
Fixpoint getNatIndex (natlist: list nat) (value: nat) (index: nat) : nat := 
  match natlist with
  | h'::t' => if (beq_nat value h') then index 
              else getNatIndex t' value (S (index))
  | nil => index
  end.

(** A helper function for selectWhere. Finds the index of the given value among a list of strings **)
Fixpoint getStringIndex (stringlist: list string) (value: string) (index: nat) : nat := 
  match stringlist with
  | h'::t' => if (beq_str value h') then index 
              else getStringIndex t' value (S (index))
  | nil => index
  end.

(** A helper function for selectWhere. Calls the two functions above to find the index of the
given value from the entire table **)
Fixpoint selectIndex (table: table)(field : string)(natval: nat)(stringval: string): nat := 
 match table with
 | cons h t => 
  match h with
  | make_col_nat natheader natlist => 
   if (beq_str (get_header_str natheader) field) 
   then getNatIndex natlist natval 0
   else selectIndex t field natval stringval 
  | make_col_string stringheader stringlist => 
   if (beq_str (get_header_str stringheader) field) 
   then getStringIndex stringlist stringval 0
   else selectIndex t field natval stringval
  end
 | nil => 0
 end.

(** A helper function for selectWhere. Returns the value, from a list of nats, at a given index. Used to help build
the return value for selectWhere **)
Fixpoint natElemAt (list: list nat) (index: nat): nat :=
 match list with
 | h::t => match index with
          | 0 => h
          | S n => natElemAt t n
          end
 | nil => 0
 end.

(** A helper function for selectWhere. Returns the value, from a list of strings, at a given index. Used to help build
the return value for selectWhere **)
Fixpoint stringElemAt (list: list string) (index: nat): string :=
 match list with
 | h::t => match index with
          | 0 => h
          | S n => stringElemAt t n
          end
 | nil => "no valid string"
 end.

Compute selectIndex table1 "id numbers" 5 "John".
Compute stringElemAt ("Bob"::"Rick"::"Matt"::nil) 1.

Compute selectIndex table1 "id numbers" 3 "test".
Compute selectIndex table1 "names" 3 "Herbert".

(** selectWhere. Takes in the full table, a second table (to recurse over), the field, a natval and a stringval. 
The function will only use one of the natval or stringval, depending on the given field's type. **)

Fixpoint selectWhere (table: table)(rec_table: list column)(field: string)(natval: nat)(stringval: string): list column := 
 match rec_table with
 | cons h t => 
  match h with
  | make_col_nat natheader natlist => 
                 make_col_nat natheader ((natElemAt natlist (selectIndex table field natval stringval))::nil)::(selectWhere table t field natval stringval)
  | make_col_string stringheader stringlist => 
                 make_col_string stringheader ((stringElemAt stringlist (selectIndex table field natval stringval))::nil)::(selectWhere table t field natval stringval)
  end
 | nil => nil
 end.

Compute selectWhere table1 table1 "id numbers" 3 "test".
(** Two of the same tables are initially passed in to the function for the following reason:
 in 'Compute selectWhere table1 table1 "id numbers" 3 "Millie"' above, we iterate over the columns in the second
table1, replacing them with columns of height=1. This changes the index of id number 3 from 2 to 0 in the resulting table, 
and thus, we would end up using the name at index 0... not the one we want. By supplying a second table to the function,
we have an unaltered reference from which we can derive the proper indicies. **)

(** helper function for the merge command that takes two columns and checks to see if
they have the same header. If they do, they will be combined into one column in the merge
function that follows **)

Definition combine_cols(c1 c2: column) : column :=
  match c1, c2 with
  | make_col_nat h1 l1, make_col_nat h2 l2 =>
        if (beq_str (get_header_str h1)(get_header_str h2)) then make_col_nat h1 (l1++l2)
        else c1
  | make_col_string h1 l1, make_col_string h2 l2 =>
        if (beq_str (get_header_str h1)(get_header_str h2)) then make_col_string h1 (l1++l2)
        else c1
  | make_col_nat _ _, make_col_string _ _ => c1
  | make_col_string _ _, make_col_nat _ _ => c1
end.

(** Merge command. Takes two tables and combines columns of the two seperate tables
 that have the same header **)

Fixpoint merge (t1 t2: table) : table :=
  match t1, t2 with
    | nil, nil => nil
    | nil, _ => t2
    | _, nil => t1
    | h::t, h'::t' => 
      match h, h' with
      | make_col_nat h1 l1, make_col_nat h2 l2 => (combine_cols h h')::(merge t t')
      | make_col_string h1 l1, make_col_string h2 l2 => (combine_cols h h')::(merge t t')
      | make_col_string _ _, make_col_nat _ _ => merge t t'
      | make_col_nat _ _, make_col_string _ _ => merge t t'
end
end.

Example table2 := column1::column2::nil.

(** This should merge the columns of table1 and table2 that have the same
headings. Thus, there will be the same number of columns in the resulting
table as the two that are being merged, but all of the data from each
table will be in one table.  **)

Compute merge table1 table2.

(** This will drop the column titled "id numbers" from table1. As a result
table1 will be left with one column, "names" **)
Compute dropcolumn table1 "id numbers".

(** the following code was found online and used as a sort function (used in drop rows)**) 
Fixpoint leqb (m n : nat) {struct m} : bool :=
  match m with
  | 0 => true
  | S m => match n with 
           | 0 => false
           | S n => leqb m n
           end
  end.

Eval compute in leqb 3 4.
Eval compute in leqb 4 3.

Fixpoint insert1 (n:nat)(ms : list nat) {struct ms} : list nat :=
  match ms with
  | nil => n::nil
  | m::ms' => if leqb n m
              then n::ms
              else m::(insert1 n ms')
  end.

Eval compute in insert1 3 (1::2::4::nil).

Fixpoint sort (ms : list nat) : list nat :=
  match ms with
  | nil => nil
  | m::ms' => insert1 m (sort ms')
  end.

Eval compute in sort (4::2::3::1::nil). 

(** end of sorting code from internet**)

Fixpoint drop_row_in_list {X:Type} (l: list X) (index : nat) (count: nat) : list X :=
                           match l with 
                                | nil => nil 
                                | cons h t => if (beq_nat index count) then t else h::(drop_row_in_list t index (count+1))
                                  end.

Definition drop_row_in_col (c: column) (index : nat) : column := 
                   match c with 
                        | make_col_nat h ln => make_col_nat h (drop_row_in_list ln index 1)
                        | make_col_string h2 ls => make_col_string h2 (drop_row_in_list ls index 1) 
                      end. 


Fixpoint drop_a_row (t : table) (index : nat) : table := 
             match t with 
               | nil => t 
               | cons current_col other_cols => (drop_row_in_col current_col index)::(drop_a_row other_cols index)
                end. 

                       
                                               
Fixpoint drop_rows_impl (t: table) (indexes : list nat) (drop_number: nat) : table := 
          match indexes with 
                | nil => t 
                | cons head tail => drop_rows_impl (drop_a_row t (head - drop_number)) tail (drop_number + 1)
                end.

Definition drop_rows (t: table) (indexes: list nat) : table := 
          drop_rows_impl t (sort indexes) 0. 


(**some examples to show the drop rows functionality**)
Example c1 := make_col_nat header1 (1::2::3::4::5::nil).
Example c2 := make_col_string header2 ("alpha"::"beta"::"charlie"::"delta"::"echo"::nil).

Example table_test := c1::c2::nil.

Compute table_test. 


Compute drop_rows table_test (2::3::nil).
Compute drop_rows table_test (1::5::3::nil). 
Compute drop_rows table_test (4::5::3::nil). 
Compute drop_rows table_test (nil).

(**end of examples to test drop rows functionality**)

(* the following functions are to implement get_rows, which we do by calling drop_rows on all 
of the rows that aren't passed to get_rows*)




(*boolean function to determine if a given nat is in a given list of nats, used in the xor function*)
Fixpoint contains (l: list nat) (n: nat) : bool := 
                match l with
                     | nil => false 
                     | h::t => if (beq_nat h n) then true else (contains t n)
                     end.

(*xor takes two lists of nats and returns the list of nats that are in either but not both.
we use this function in our implementation of get_rows, which we do by dropping all the rows that 
we don't want to get*)
 
Fixpoint xor (l1: list nat) (l2: list nat) : list nat := 
                    match l1 with 
                         | nil => nil
                         | h::t => if (contains l2 h) then xor t l2 else h::(xor t l2)
                           end.

(*demonstrating the xor functionality*)

Compute xor (1::2::5::7::2::1::8::nil) (1::2::4::1::6::8::nil).

(*helper function for length_impl*)  

Fixpoint length_impl {X : Type} (l: list X) (start: nat) : nat := 
       match l with  
         | nil => start 
         | h::tail => length_impl tail (start + 1)
          end.

(*function to determine the length of a table, where the length is defined as the number of rows*)

Definition length (t: table) : nat := 
            match t with 
                | nil => 0
                | h::t => match h with 
                              | make_col_nat hd1 ln1 => length_impl ln1 0
                              | make_col_string hd2 ln2 => length_impl ln2 0
                              end  
                  end.

(*helper function for length_list*)

Fixpoint length_list_impl (n : nat) (count: nat) : list nat := 
           match n with 
               | O => nil 
               | S n' => (count::(length_list_impl n' (count+1)))
                  end.

(*function to create a list nat from 1 to the specified length with every nat in between*)
Definition length_list (n: nat) : list nat := 
              length_list_impl n 1. 

(*demonstrating the above functionality*)

Compute length_list 10.
Compute length table_test.     


(*the get_rows function is implemented using the drop_rows function. We use the xor function to 
 produce a list of nats that represent all of the rows you don't want to get, and simply drop those rows
to produces to the desired new table*)   

Definition get_rows (t: table) (indexes: list nat) : table := 
        drop_rows t (xor (length_list (length t)) (indexes)).

(**same as dropping all the rows you don't want to get**)

(*demonstrating the functionality of get_rows*)
Compute get_rows table_test (1::3::5::nil).


(*the following several functions are all to implement an innerjoin, which takes two tables, 
 a join column from the first table, and a join column from the second table, and produces a 
new table which consists of rows comprised of all column types from the first and second tables. 
For all rows in the new table, the values of the columns from the specified join columns are equal. 
This implementation is designed to join on a single column from each table*)  





(*function to take two rows and combine them into a larger row. treating a row as a table, and assuming its of length 1*)
Fixpoint merge_rows (t1: table) (t2: table) : table := 
                match t1, t2 with
               | nil, nil => nil 
               | nil, _ => t2 
               | _, nil => t1 
               | h::tail, _ => h::(merge_rows (tail) (t2)) 
                end. 


(*demonstrating the functionality of merge_rows*)
Example header3 := make_header "age". 
Example c5 := make_col_nat header3 (30::nil). 
Example c6 := make_col_nat header1 (2::nil). 
Example c7 := make_col_string header2 ("steve"::nil). 
Example header4 := make_header "eye_color". 
Example c8 := make_col_string header4 ("brown"::nil).
 

Example row :=  c5::c7::nil. 
Example row2 := c6::c8::nil. 


Compute row. 
Compute row2. 
Compute merge_rows row row2.

(*natprod is the same as we defined it in class*)
Inductive natprod : Type :=
  pair : nat -> nat -> natprod.


(** similar to getNatIndex, except it returns a list of all of the indices where the given nat value is equal
to a value in the list of strings**)

Fixpoint getNatIndices (natlist: list nat) (value: nat) (index: nat) : list nat := 
  match natlist with
  | h'::t' => if (beq_nat value h') then index::(getNatIndices t' value (index + 1)) 
              else getNatIndices t' value (S (index))
  | nil => nil
  end.

(** similar to getStringIndex, except it returns a list of all of the indices where the given string value is equal
to a value in the list of strings**)
Fixpoint getStringIndices (stringlist: list string) (value: string) (index: nat) : list nat := 
  match stringlist with
  | h'::t' => if (beq_str value h') then index::(getStringIndices t' value (index + 1)) 
              else getStringIndices t' value (S (index))
  | nil => nil
  end.

(*function to take list of natprods and return a list of nats, where the nats are the 
second values from each natprod in the given list of natprods. *)

Fixpoint get_second_val (l : list natprod) : list nat := 
                  match l with 
                      | nil => nil 
                      | (pair h t)::tail => t::(get_second_val tail)
                        end.

(*function to take a given nat and list of nats, and return a list of natprods 
equal to the length of the given list of nats, in which the first element of every natprod 
is the given nat and the second value is the value from the given list of nats that is at the 
position in the list as the new list. for example, stich 1, 1::2::4::nil would yeild (1,1)::(1,2)::1,4)::nil*)  

Fixpoint stitch (n: nat) (l : list nat) : list natprod := 
        match l with
          | nil => nil 
          | h::t => (pair n h)::(stitch n t)   
           end.

(*function to combine two natprod's, based on the function app that we defined in class*)

Fixpoint appNatProd (l1 l2 : list natprod)
                : (list natprod) :=
  match l1 with
  | nil  => l2
  | cons h t => cons h (app t l2)
  end.  



(*the following four function are the helper functions and functions for getting the tuples 
that tell us which rows to merge together from the specified columns. There's a version for 
both constructors of columns, one of which relies on getNatIndices and the other on getStringIndices.
The value 1 is passed to both functions as the starting index, because the first row in a table is 
considered row 1*) 
 
Fixpoint get_tuples_from_list_nat_impl (l1: list nat) (l2: list nat) (index: nat) : list natprod := 
              
                         match l1 with
                              | nil => nil
                              | h::t =>  match (getNatIndices l2 h 1) with 
                                          | nil => get_tuples_from_list_nat_impl t l2 (index+1)
                                          | _ => appNatProd(stitch index (getNatIndices l2 h 1)) (get_tuples_from_list_nat_impl t l2 (index+1))  
                                                              end
                                end. 
                           


Definition get_tuples_from_list_nat (l1: list nat) (l2: list nat) : list natprod := 
                    get_tuples_from_list_nat_impl l1 l2 1. 
          
Fixpoint get_tuples_from_list_string_impl (l1: list string) (l2: list string) (index: nat) : list natprod := 
              
                         match l1 with
                              | nil => nil
                              | h::t =>  match (getStringIndices l2 h 1) with 
                                          | nil => get_tuples_from_list_string_impl t l2 (index+1)
                                          | _ => appNatProd(stitch index (getStringIndices l2 h 1)) (get_tuples_from_list_string_impl t l2 (index+1))  
                                                              end
                                end.



Definition get_tuples_from_list_string (l1: list string) (l2: list string) : list natprod := 
                    get_tuples_from_list_string_impl l1 l2 1. 
          


(* at the heart of the implenetation of inner join, get_tuples take two columns and returns the list 
of pairs that represent which rows should be merged together in the new table, based on the equivalency of 
values in the specified columns to join on *)

Definition get_tuples (col1: column) (col2: column) : list natprod:=
                    match col1 with
                         | make_col_nat hd1 ln1 => match col2 with 
                                                         | make_col_nat hd2 ln2 => get_tuples_from_list_nat ln1 ln2
                                                         | _ => nil
                                                        end  
                         | make_col_string hd3 ln3 => match col2 with 
                                                         | make_col_string hd4 ln4 => get_tuples_from_list_string ln3 ln4
                                                         | _ => nil
                                                          end
                                     end.




(*demonstrating the functionality of get_tuples*)

Example c9 := make_col_nat header1 (3::2::2::4::1::nil).

Compute c1.
Compute c9.
Compute get_tuples c1 c9.



(*this function is the implementation of inner join. The function relies on being passed the 
list of natprods that tell which rows to join together. For example, (1,2) would mean row 1 from 
the first table and row 2 from the second. It merges the specified rows from each table using the 
function merge_rows, and puts all these rows together into a single table using the function merge*)

Fixpoint do_inner_join (t1: table) (t2: table) (key: list natprod) : table :=
          match key with
           | nil => nil 
           | (pair r1 r2)::ktail => merge (merge_rows (get_rows t1 (r1::nil)) (get_rows t2 (r2::nil))) (do_inner_join t1 t2 ktail)
              end.


  
(*final inner join function, which simply calls the function do_inner_join, which is passed the list of 
  natprods produced from calling the function get_tuples on the two columns chosen to join on*)

Definition inner_join (t1: table) (t2: table) (col1 : column) (col2 : column) : table := 
                     do_inner_join t1 t2 (get_tuples (col1) (col2)).  
         






(*Example of inner join working. In this example, table A has names and ID numbers, and table B has 
names and dates (represented simply as strings), the inner join joins on the column for names in each. Notice that Mike appears in the resulting table twice, 
as one would expect with an inner join, because he is in table B twice. *)

Example names_header := make_header "Names". 
Example ID_header := make_header "ID".
Example date_header := make_header "Date".

Example A_names := make_col_string names_header ("Mike"::"Kyle"::"Adam"::"Ricky"::"Morty"::nil). 
Example A_id := make_col_nat ID_header (1::2::3::4::5::nil). 

Example B_names := make_col_string names_header ("Mike"::"Steve"::"Mike"::"Bob"::"Kyle"::nil). 
Example B_date := make_col_string date_header ("1/1/2014"::"2/1/2014"::"3/1/2014"::"4/1/2014"::"5/1/2014"::nil).

Example table_A := A_names::A_id::nil. 
Example table_B := B_names::B_date::nil.

Compute table_A. 
Compute table_B. 

Compute inner_join table_A table_B A_names B_names.



(*the below work is to implement a natural join, which we represent as an extention of an inner join,
where the columns to join on from each table are not manually entered, but rather are determined automatically 
based on the which column in each table has the same column header as another column in the other table*)




(*our representation of a null header and null column, since some of the helper functions are required 
to return a column header or null and there is no null constructor for either of those*)
 
Definition NULL_Header := make_header "NULL". 
Definition NULL_Col := make_col_string NULL_Header nil.


(*function to return a list of the column headers in a given table. This is necessary for use in later
functions to compare two lists of headers (instead of tables directly) to determine which column header, and 
 ultimately what column, should be joined on in a natural join*)

Fixpoint get_table_headers (t: table) : list col_header :=
            match t with 
              | nil => nil
              | col_head::col_tail => match col_head with 
                                       | make_col_nat hd1 ln1 => hd1::(get_table_headers col_tail)
                                       | make_col_string hd2 ln2 => hd2::(get_table_headers col_tail)
                                           end
              end.

(*function to determine whether two headers are equal. We define headers as equal if they are created
 using the same string (make_header is the only possible constructor for a header*) 

Definition beq_header (h1: col_header) (h2: col_header) : bool :=
               match h1 with 
                    | make_header string1 => match h2 with 
                                                  | make_header string2 => beq_str string1 string2
                                                             end 
                    end.

(*boolean function to determine whether or not a column header is in a list of column headers. 
 this function is neccessary to implement the logic of the function that chooses which column header 
 corresponds to the column to join on in a natural join*)   

Fixpoint contains_header (h: col_header) (lh: list col_header) : bool := 
                              match lh with 
                                 | nil => false 
                                 | head::tail => if(beq_header h head) then true else contains_header h tail
                                end.  


(*function that implements the logic of automatically choosing which column to join on in a natural join. 
 A special "NULL_Header" was created in the event that there was no appropriate column to join on, since
the function has to return a column header. It relies on the logic of contains_header, and essentially choose 
 a column header from the first list that also appears in the second list. This will only work as in intentioned 
when there is a single common header in the two lists*) 

Fixpoint get_natural_header (lh1: list col_header) (lh2: list col_header) : col_header :=
               match lh1 with 
                 | nil => NULL_Header 
                 | h::t => if(contains_header h lh2) then h else get_natural_header t lh2          
                     end. 
                   




(*function to get a column in a table with a specified header, which is necessary for the get_natural_col
 function, and ultimately a natural join, to work*)

Fixpoint get_col_from_header (t : table) (head:col_header) : column :=  
                              match t with 
                               | nil => NULL_Col 
                               | c1::ct => match c1 with 
                                            | make_col_nat hd ln => if(beq_header hd head) then c1 else get_col_from_header ct head
                                            | make_col_string hd ln => if(beq_header hd head) then c1 else get_col_from_header ct head              
                                                     end
                                 end.

(*function to return which column to join on in a natural join. relies on get_natural_headers to do the implementation,
 and using the function get_table_headers to get a list of table headers from a table*)

Definition get_natural_col (t1 : table) (t2: table) : column := 
           get_col_from_header t1 (get_natural_header (get_table_headers t1) (get_table_headers t2)).
             


(*below is the natural join function. it essentially calls inner join, and automatically
 determines the two parameters that specify which columns to join on using a helper function 
  get_natural col. This is designed for there being only one overlapping column in the two tables,
  and is not built to handle multiple columns with equal headers*)
                                 
Definition natural_join (t1: table) (t2: table) : table := 
           inner_join t1 t2 (get_natural_col t1 t2) (get_natural_col t2 t1).                         
                         


Compute table_A. 
Compute table_B. 
Compute inner_join table_A table_B A_names B_names.
Compute natural_join table_A table_B.
(* notice that the results for the inner join and natural join are the same, 
but for natural join the function automatically determined which columns to join on 
whereas they had to be specified in inner_join. *)

(*the following functions are to implement another query function, which returns all the rows 
in a given table, where the values in a specified column meet a specified condition. There are two 
different functions, one for use when the column is composed of strings, and the other nats.*)


Fixpoint leq_bool (n: nat) (n2: nat) : bool :=  
                match n with 
                     | O => true 
                     | S n' => match n2 with  
                                   | O => false 
                                   | S n2' => leq_bool n' n2'
                                      end
                       end. 

Fixpoint getNatIndices' (eq: nat->nat->bool) (l: list nat) (value: nat) (index: nat) : list nat := 
  match l with
  | h'::t' => if (eq h' value) then index::(getNatIndices' eq t' value (index + 1)) 
              else getNatIndices' eq t' value (S (index))
  | nil => nil
  end.

Fixpoint getStringIndices' (eq: string->string->bool) (l: list string) (value: string) (index: nat) : list nat := 
  match l with
  | h'::t' => if (eq h' value) then index::(getStringIndices' eq t' value (index + 1)) 
              else getStringIndices' eq t' value (S (index))
  | nil => nil
  end.



Example l1 := length_list 10. 
Compute l1.
Compute getNatIndices' leq_bool l1 6 1. 



Definition getWhereNat (t: table) (c: column) (f: nat->nat->bool) (value: nat) : table := 
                    match c with 
                          | make_col_nat head1 ln => get_rows t (getNatIndices' f ln value 1) 
                          | _ => nil 
                        end.

Compute table_test. 
Compute getWhereNat table_test c1 leq_bool 3.  
           

Definition getWhereString (t: table) (c: column) (f: string->string->bool) (value: string) : table := 
                    match c with 
                          | make_col_string head1 ls => get_rows t (getStringIndices' f ls value 1) 
                          | _ => nil 
                        end.