import java.awt.Color;
import java.awt.Dimension;
import java.awt.Graphics;

import javax.swing.JFrame;
import javax.swing.JPanel;

public class GraphicUI extends JFrame{
	
	private Distributor d;
	private final static int N_CARS = 10;
	
	public GraphicUI(){
		
		this.setTitle("Fair distribution");
		this.setPreferredSize(new Dimension(800, 600));
        this.pack();
        this.setVisible(true);
        this.setDefaultCloseOperation(EXIT_ON_CLOSE);

		d = new Distributor();
		
		for(int i=0; i<N_CARS; i++){
			d.addCar(new Car());
			d.getCar(i).move();
		}
	}
	
	@Override
	public void paint(Graphics g){
		
		g.setColor(Color.BLUE);
		for(int i=0; i<N_CARS; i++)
			g.fillOval(this.d.getCar(i).getX(), this.d.getCar(i).getY(), 10, 10);
	}
	
	public void clearSurface(Graphics g) throws InterruptedException{
		getContentPane().removeAll();
		getContentPane().repaint();
		Thread.sleep(200);
	}

	public static void main(String[] args) throws InterruptedException {
		
		GraphicUI gui = new GraphicUI();
		int num;
		int k=0;
		
		while(true){
			
			gui.clearSurface(gui.getGraphics());
			gui.paint(gui.getGraphics());
			Thread.sleep(500);
			
			// scelgo le 0 < x < 20 macchine da spostare (a caso)
			num = (int) (Math.random() * 1000 % N_CARS);
			
			// mettere num = N_CARS assicura che tutte le auto vengano posizionate scegliendo la distribuzione equa
			//num = N_CARS;
			 
			 // sposto le x macchine
			 for(int i=0; i<num; i++)
				 gui.d.getCar((int)(Math.random() * 1000 % N_CARS)).move();
			 
			// scelgo le 0 < y < 20 macchine da spostare per garantire la fair distribution
			 num = (int) (Math.random() * 1000 % N_CARS);
			
			 //num = N_CARS;
			// sposto le y macchine
			for(int i=0; i<num; i++)
				gui.d.findNewPosition(gui.d.getCar((int)Math.random() * 1000 % N_CARS));
			 
			 gui.paint(gui.getGraphics());
			 //gui.clearSurface(gui.getGraphics());
			 k++;
		}
		
		//gui.setVisible(true);
	}
}