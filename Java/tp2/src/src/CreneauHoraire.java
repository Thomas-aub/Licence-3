package src;
import java.util.Scanner;

public class CreneauHoraire {

    protected int j, h, m, d;

    public CreneauHoraire(int j, int h, int m, int d){
        this.j = j;
        this.h = h;
        this.m = m;
        this.d = d;
    }



    public boolean equals(CreneauHoraire b){
        return ((this.j == b.j) & (this.h == b.h) & (this.m == b.m) & (this.d == b.d));
    }

    public static CreneauHoraire newCreneauHoraire(){

        Scanner in = new Scanner(System.in);

        System.out.print("Jour: ");
        int j = in.nextInt();
        System.out.print("Heure: ");
        int h = in.nextInt();
        System.out.print("Minute: ");
        int m = in.nextInt();
        System.out.print("Durée: ");
        int d = in.nextInt();

        in.close();

        CreneauHoraire c1 = new CreneauHoraire(j,h,m,d);
        return c1;
    }

    public CreneauHoraire clone(){
        CreneauHoraire c1 = new CreneauHoraire(this.j, this.h, this.m, this.d);
        return c1;
    }






    public int getJ() {
        return j;
    }

    public int getH() {
        return h;
    }

    public int getM() {
        return m;
    }

    public int getD() {
        return d;
    }


    public void setJ(int j) {
        this.j = j;
    }

    public void setH(int h) {
        this.h = h;
    }

    public void setM(int m) {
        this.m = m;
    }

    public void setD(int d) {
        this.d = d;
    }


    @Override
    public String toString() {
        return "CreneauHoraire{" +
                "j=" + j +
                ", h=" + h +
                ", m=" + m +
                ", d=" + d +
                '}';
    }


}
