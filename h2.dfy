
datatype Pair = Pair(key:int, val:char)

class HashMap{
    var hashmap:array<seq<Pair>>;
    var arrSize:int;
    var arrCapacity:int;

    predicate Valid() 
    reads this, hashmap
      {
        0 <= arrSize <= arrCapacity && arrCapacity == hashmap.Length && arrCapacity > 0 
      }

    constructor Init(c:int)
        requires c > 0
        ensures Valid()
        ensures arrCapacity == c && arrSize == 0
        ensures fresh(hashmap)
      {
        hashmap := new seq<Pair>[c];
        arrCapacity := c;
        arrSize := 0;
      }


     function method getIndex(key:int):(int) 
        requires Valid()
        reads this, hashmap
        ensures 0 <= getIndex(key) < arrCapacity
     {
       var result:int := 0;
        
       if (key >= 0)
       then key % arrCapacity
       else (key * -1) % arrCapacity
      }

    method put(k:int, v:char)
        requires Valid()
        modifies this, hashmap, `arrSize
        requires arrSize < arrCapacity
        ensures Valid()
        {

          var i:int := getIndex(k);
          var ii : seq<Pair> := hashmap[i];
          if(|ii| == 0){
              ii := ii + [Pair(k,v)];
              arrSize := arrSize +1;
          }else{
            var l := 0;
            while l < |ii| && |ii|>0
              decreases |ii| - l
              invariant |ii| > 0
              invariant l <= |ii|
              invariant forall x :: 0<=x<l ==> ii[x].key != k
              {              
                if(ii[l].key == k){
                  return;
                }
                l:= l+1;
              }
            ii := ii + [Pair(k,v)];
            return;
          }
      }


      method contains(k:int) returns(z:bool)
      requires Valid();
      ensures z == true ==> exists x,y :: 0<=x<arrCapacity && 0<=y<|hashmap[x]| && hashmap[x][y].key == k 
      ensures Valid();
      {
        var i:= getIndex(k);
        var ii := hashmap[i];
        if |ii| == 0{
            return false;
        }
        assert |ii| > 0;        
        var l := 0;
        while l < |ii| && |ii|>0
            decreases |ii| - l
            invariant |ii| > 0
            invariant l <= |ii|
            invariant forall x :: 0<=x<l ==> ii[x].key != k
            {              
                if(ii[l].key == k){
                return true;
                }else{
                l:= l+1;
                }
                
            }       
        return false;
      }


      method get(k:int, def:char) returns(v:char)
      requires Valid();
      ensures Valid();
      ensures v != def ==> exists x,y :: 0<=x<arrCapacity && 0<=y<|hashmap[x]| && hashmap[x][y].key == k 
      { 
        var c := contains(k);
        if(c){
            var i:= getIndex(k);
            var ii := hashmap[i];
            assume |ii| > 0;
            var l := 0;
            while l < |ii|
            decreases |ii| - l
            invariant |ii| > 0
            invariant l <= |ii|
            invariant forall x :: 0<=x<l ==> ii[x].key != k
            {              
                if(ii[l].key == k){
                var v := ii[l].val;
                return v;
                }else{
                l:= l+1;
                }
                
            }       
        }
        return def;
      }    
      
}