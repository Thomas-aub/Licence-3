import java.util.ArrayList;
import java.util.List;

public class JoueurAleatoire extends Joueur{
    public JoueurAleatoire(int _id) {
        super(_id);
    }

    public Coup getCoup(Plateau _etatJeu){
        int rand = Tool.monRandom(0,_etatJeu.getCasesLibres().size());
        assert rand < _etatJeu.getCasesLibres().size();
        int[] tmp = _etatJeu.getCasesLibres().get(rand);
        Coup c = new Coup(tmp[0],tmp[1]);

        return c;
    }
}
