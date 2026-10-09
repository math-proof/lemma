function cmp(intRange, offset){
	var [start, stop] = intRange;
	if (start > offset)
		return 1;

	if (stop <= offset)
		return -1;

	return 0;
}

export function textarea_textContent(textarea) {
	return textarea.value.split('\n');
}

export function textarea_selection_range(textarea, text){
	var selectionStart = textarea.selectionStart;
	var selectionEnd = textarea.selectionEnd;

	if (text == null)
		text = textarea_textContent(textarea);

	var intervals = [];
	var start = 0;
	for (var tex of text){
		var stop = start + tex.length + 1;
		intervals.push([start, stop]);
		start = stop;
	}

	var lineStart = intervals.binary_search(selectionStart, cmp);
	var offsetStart = selectionStart - intervals[lineStart][0];

	if (selectionEnd == selectionStart){
		var lineStop = lineStart + 1;
		var offsetStop = offsetStart;
	}
	else{
		var lineStop = intervals.binary_search(selectionEnd - 1, cmp) + 1;
		var offsetStop = selectionEnd - intervals[lineStop - 1][0];
	}

	return {lineStart, lineStop, offsetStart, offsetStop};
}

export function last_line_offset(textarea){
	var text = textarea_textContent(textarea);
	var {lineStart, lineStop, offsetStart, offsetStop} = textarea_selection_range(textarea, text);
	if (lineStop == text.length)
		return offsetStop;
}

export function head_line_offset(textarea){
	var text = textarea_textContent(textarea);
	var {lineStart, lineStop, offsetStart, offsetStop} = textarea_selection_range(textarea, text);
	if (!lineStart)
		return offsetStart;
}

export function line_offset(textarea){
	var text = textarea_textContent(textarea);
	var {lineStart, lineStop, offsetStart, offsetStop} = textarea_selection_range(textarea, text);
	return offsetStart;
}

export function get_indices(textarea){
	var text = textarea_textContent(textarea);
	var {lineStart, lineStop, offsetStart, offsetStop} = textarea_selection_range(textarea, text);
	return [lineStart, offsetStart];
}

export function is_last_char(textarea){
	var text = textarea_textContent(textarea);
	var {lineStart, lineStop, offsetStart, offsetStop} = textarea_selection_range(textarea, text);
	return lineStop == text.length && offsetStop == text[lineStop - 1].length;
}

export function is_head_char(textarea){
	var text = textarea_textContent(textarea);
	var {lineStart, lineStop, offsetStart, offsetStop} = textarea_selection_range(textarea, text);
	return !lineStart && !offsetStart;
}

export function set_focus(textarea, row, selectionStart, focus){
	var text = textarea_textContent(textarea);
	if (row < 0)
		row += text.length;

	for (var i of range(Math.min(row, text.length))) {
		selectionStart += text[i].length + 1;
	}

	textarea.selectionStart = selectionStart;
	textarea.selectionEnd = selectionStart;
	if (focus == null || focus)
		textarea.focus();
}

console.log('import textarea.js');