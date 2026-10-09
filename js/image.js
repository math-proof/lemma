console.log('import image.js');

//precondition: deg == 90 || deg == -90
export function rotateImage(img, width, height, deg, ext){
	ext ||= 'jpeg';

	var canvas = document.createElement('canvas');
	canvas.width = height;
	canvas.height = width;

	var ctx = canvas.getContext("2d");
	ctx.clearRect(0, 0, height, width);

	ctx.translate(height, 0);

	ctx.rotate(deg * Math.PI / 180);

	var [x, y] = deg > 0? [0, 0]: [-width, -height];
	ctx.drawImage(img, 0, 0, width, height, x, y, width, height);

	return canvas.toDataURL(`image/${ext}`);
}