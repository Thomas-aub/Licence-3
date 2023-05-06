import java.util.ArrayList;
import java.util.List;

public abstract class Joueur {
    private int id;
    private List<int[]> coupJoue = new ArrayList<int[]>();

    public Joueur(int _id) {
        this.id = _id;
    }

    public int getId() {
        return id;
    }

    public List<int[]> getCoupJoue() {
        return coupJoue;
    }

    public void addCoupJoue(Coup c) {
        this.coupJoue.add(new int[] {c.getX(),c.getY()});
    }

    public abstract Coup getCoup(Plateau _etatJeu);
}
