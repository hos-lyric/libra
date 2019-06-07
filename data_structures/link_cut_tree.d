// Link-Cut Tree
//   Modify val and update to the data needed
class Tree {
  Tree l, r, p;
  int size;
  int id;
  int[] val;
  this(int id) {
    l = r = p = null;
    size = 1;
    this.id = id;
    val = [id];
  }
  void update() {
    size = (l ? l.size : 0) + 1 + (r ? r.size : 0);
    val = (l ? l.val : []) ~ [id] ~ (r ? r.val : []);
  }
  bool isRoot() const {
    return (!p || (p.l != this && p.r != this));
  }
  void rotate() {
         if (p.l == this) { if (r) { r.p = p; } p.l = r; r = p; }
    else if (p.r == this) { if (l) { l.p = p; } p.r = l; l = p; }
    Tree pp = p.p;
    if (pp) {
           if (pp.l == p) pp.l = this;
      else if (pp.r == p) pp.r = this;
    }
    p.update(); p.p = this; p = pp;
  }
  void splay() {
    for (; !isRoot(); rotate()) {
      if (!p.isRoot()) ((p.l == this) == (p.p.l == p)) ? p.rotate() : rotate();
    }
    update();
  }

  // Make the path from v to the root solid
  // Return the node where it entered the last solid path
  Tree expose() {
    Tree u = this, v = null;
    for (; u; u = u.p) { u.splay(); u.r = v; u.update(); v = u; }
    splay();
    return v;
  }

  // parent of this := u
  void link(Tree u) {
    expose(); u.expose(); p = u; u.r = this; u.update();
  }

  // parent of this := null
  void cut() {
    expose(); l.p = null; l = null; update();
  }

  // the root of the tree this belongs
  Tree root() {
    expose();
    for (Tree u = this; ; u = u.l) if (!u.l) { u.splay(); return u; }
  }

  // LCA of this and u
  //   Assume this.root == u.root
  Tree lca(Tree u) {
    expose(); return u.expose();
  }

  // ([child of LCA, ..., this], [LCA, ..., u])
  //   Assume this.root == u.root
  import std.typecons : Tuple, tuple;
  Tuple!(int[], int[]) path(Tree u) {
    expose(); Tree v = u.expose(); splay(); v.splay();
    auto pathT = (v == this) ? [] : ((l ? l.val : []) ~ [this.id]);
    auto pathU = [v.id] ~ (v.r ? v.r.val : []);
    return tuple(pathT, pathU);
  }
}
void print(in Tree[] nodes) {
  import std.stdio : write, writeln;
  import std.string : format;
  string dfs(in Tree u) {
    return format("<%s%s(%s, %s)%s>",
        u.l ? (dfs(u.l) ~ " ") : "",
        u.id, u.size, u.val,
        u.r ? (" " ~ dfs(u.r)) : "");
  }
  foreach (u; nodes) {
    if (u.isRoot()) {
      write("| ");
      if (u.p) write(u.p.id, " ");
      write("<- ", u.id, ": ");
      writeln(dfs(u));
    }
  }
}

unittest {
  import std.stdio : writeln;

  int[] par;
  Tree[] nodes;
  void link(int a, int b) {
    par[a] = b;
    nodes[a].link(nodes[b]);
  }
  void cut(int a) {
    par[a] = -1;
    nodes[a].cut();
  }
  void query(int a, int b) {
    int[] pathA;
    for (int u = a; u != -1; u = par[u]) {
      pathA = u ~ pathA;
      int[] pathB;
      for (int v = b; v != -1; v = par[v]) {
        pathB = v ~ pathB;
        if (u == v) {
          writeln(a, " ", b, ": ", pathA, " ", pathB);
          const res = nodes[a].path(nodes[b]);
          assert(pathA[1 .. $] == res[0]);
          assert(pathB == res[1]);
          return;
        }
      }
    }
    writeln(a, " ", b, ": different root");
    assert(nodes[a].root() != nodes[b].root());
  }

  // https://www.ioi-jp.org/camp/2013/2013-sp-tasks/2013-sp-day4.pdf
  enum n = 9;
  par = new int[n];
  par[] = -1;
  nodes = new Tree[n];
  foreach (u; 0 .. n) {
    nodes[u] = new Tree(u);
  }
  link(1, 2);
  link(6, 5);
  link(7, 8);
  query(5, 6);
  link(5, 4);
  link(8, 1);
  query(7, 2);
  query(3, 8);
  query(1, 8);
  link(3, 2);
  link(4, 1);
  query(8, 5);
  query(4, 3);
  cut(4);
  query(6, 8);
  link(2, 5);
  query(6, 8);
  cut(8);
  query(1, 4);
  query(6, 8);
  query(6, 3);
  cut(3);
  query(1, 2);
  link(4, 3);
  query(2, 6);
  link(8, 3);
  query(1, 7);
  query(1, 6);
  query(5, 4);
  cut(2);
  cut(5);
  link(3, 6);
  link(2, 7);
  query(1, 4);
  query(1, 5);
  query(6, 7);
  nodes.print;
}

void main() {
}
